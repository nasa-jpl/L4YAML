#!/usr/bin/env python3
"""Convert the Verso blueprint HTML into a single, paginated PDF.

Usage:
  python3 scripts/html-to-pdf.py HTML_INPUT OUTPUT_PDF

HTML_INPUT may be either
  * a single self-contained page (e.g. `_out/blueprint/html-single/index.html`),
    which is rendered directly — this is the preferred source, since Verso emits it
    in document order; or
  * a multi-page site directory (e.g. `_out/blueprint/html-multi`), whose chapter and
    section `index.html` files are discovered and merged.

Adapted from the L4YAML `scripts/html-to-pdf.py`; generalized to accept a single page
and to skip Verso's `find/`/`search/`/`-verso-*` utility directories when merging.

Requires: weasyprint (pip3 install weasyprint)
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

# Verso renders the numbered table of contents on every page as rows of the form
#   <td class="num">3.2.1.</td><td><a href="...">Title</a>
# Each page expands its own subsections, so the union of these rows across all pages
# is the full TOC. We order the merge by the *dotted section number* (true document
# order), not alphabetically, and include only pages that appear in the TOC — so the
# search/index/report/dependency-graph/blueprint-summary pages, which are not numbered
# content sections, are left out of the PDF.
_NAV_ROW = re.compile(r'<td class="num">([\d.]+)</td>\s*<td><a href="([^"]+)"')


def _resolve_page(from_index: Path, href: str, root: Path) -> Path | None:
    """Resolve a nav href (relative to the page it appears on) to an index.html file
    under `root`, or None if it points outside the site."""
    target = href.split("#")[0].split("?")[0]
    if not target:
        return None
    dest = (from_index.parent / target).resolve()
    if dest.is_dir():
        dest = dest / "index.html"
    try:
        dest.relative_to(root.resolve())
    except ValueError:
        return None
    return dest if dest.is_file() else None


def find_all_pages(html_input: Path) -> list[Path]:
    """Return the ordered list of HTML pages to render.

    A single file is returned as-is (it already holds the whole document in order).
    A multi-page site directory is ordered by its numbered table of contents.
    """
    if html_input.is_file():
        return [html_input]

    root = html_input
    root_index = root / "index.html"
    if not root_index.is_file():
        print(f"Error: {root_index} not found", file=sys.stderr)
        sys.exit(1)

    def numkey(n: str) -> tuple:
        return tuple(int(x) for x in n.strip(".").split("."))

    # Collect num -> resolved page across every page's nav; keep the lowest number
    # seen for each page (so a page shared by 3.4 and its 3.4.1 child sorts at 3.4).
    page_of_num: dict[str, Path] = {}
    for idx in sorted(root.rglob("index.html")):
        text = idx.read_text(encoding="utf-8", errors="ignore")
        for num, href in _NAV_ROW.findall(text):
            page = _resolve_page(idx, href, root)
            if page is not None:
                page_of_num.setdefault(num.strip("."), page)

    pages = [root_index]
    seen = {root_index.resolve()}
    for num in sorted(page_of_num, key=numkey):
        page = page_of_num[num]
        rp = page.resolve()
        if rp not in seen:
            seen.add(rp)
            pages.append(page)

    if len(pages) == 1:
        print(
            "warning: no numbered table-of-contents found; rendering the root page only",
            file=sys.stderr,
        )
    return pages


def merge_html(pages: list[Path]) -> str:
    """Create a single HTML document from one or more pages for PDF rendering."""
    from html.parser import HTMLParser

    class BodyExtractor(HTMLParser):
        def __init__(self):
            super().__init__()
            self.in_body = False
            self.depth = 0
            self.body_content = []
            self.head_content = []
            self.in_head = False

        def handle_starttag(self, tag, attrs):
            if tag == "body":
                self.in_body = True
                self.depth = 0
                return
            if tag == "head":
                self.in_head = True
                return
            if self.in_body:
                self.depth += 1
                attr_str = "".join(f' {k}="{v}"' for k, v in attrs)
                self.body_content.append(f"<{tag}{attr_str}>")
            if self.in_head:
                attr_str = "".join(f' {k}="{v}"' for k, v in attrs)
                self.head_content.append(f"<{tag}{attr_str}>")

        def handle_startendtag(self, tag, attrs):
            attr_str = "".join(f' {k}="{v}"' for k, v in attrs)
            if self.in_body:
                self.body_content.append(f"<{tag}{attr_str}/>")
            elif self.in_head:
                self.head_content.append(f"<{tag}{attr_str}/>")

        def handle_endtag(self, tag):
            if tag == "body":
                self.in_body = False
                return
            if tag == "head":
                self.in_head = False
                return
            if self.in_body:
                self.body_content.append(f"</{tag}>")
                self.depth -= 1
            if self.in_head:
                self.head_content.append(f"</{tag}>")

        def handle_data(self, data):
            if self.in_body:
                self.body_content.append(data)
            if self.in_head:
                self.head_content.append(data)

    # Extract head from first page only (for styles)
    first_parser = BodyExtractor()
    first_parser.feed(pages[0].read_text(encoding="utf-8"))
    head_html = "".join(first_parser.head_content)

    # Extract body from all pages
    body_parts = []
    for i, page in enumerate(pages):
        parser = BodyExtractor()
        parser.feed(page.read_text(encoding="utf-8"))
        content = "".join(parser.body_content)
        if i > 0:
            body_parts.append('<div style="page-break-before: always;"></div>')
        body_parts.append(f'<section class="chapter">{content}</section>')

    pdf_css = """
    <style>
      @page {
        size: letter;
        margin: 2cm 1.8cm 2cm 1.8cm;
        @bottom-center { content: counter(page); font-size: 9pt; color: #666; }
      }

      /* ── Hide web-only chrome ── */
      header,
      nav#toc,
      nav.toc,
      #toc,
      .toc-backdrop,
      .prev-next-buttons,
      .nav_buttons,
      .permalink-widget,
      label#toggle-toc-click,
      #toggle-toc,
      .search-box,
      .search-wrapper,
      .bp_inline_preview_panel,
      script,
      template,
      /* The embedded Lean-declaration body (the raw docstring, plus the
         auto-generated Fields / Constructors / Methods breakdown that Verso emits
         for a *structure* as stray top-level <h1>s) duplicates the rendered
         statement and corrupts the outline — drop the whole body, keeping the
         rendered statement and the declaration signature. */
      .bp_external_decl_body,
      pre.docstring,
      /* The interactive blueprint dashboards — the dependency graph and the status
         summary ("By parent groups", "Missing owner", "Untagged", with their
         embedded per-declaration Fields/Constructors panels) — are web-only views,
         not print content. Hiding them also removes their headings from the PDF
         outline (display:none generates no bookmarks) and trims the bloat. */
      [class*="bp_graph"],
      [class*="bp_summary"],
      [id$="--Dependency-Graph"],
      [id$="--Blueprint-Summary"] { display: none !important; }

      /* ── Undo the sidebar-offset layout ── */
      .with-toc { margin-top: 0 !important; }
      .with-toc > main { padding-left: 0 !important; }
      .content-wrapper { max-width: 100% !important; padding: 0 !important; }
      main { margin: 0 !important; max-width: 100% !important; }

      /* ── Typography ── */
      body {
        font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
        font-size: 11pt;
        line-height: 1.5;
        color: #222;
      }
      h1 { font-size: 18pt; page-break-before: always; margin-top: 0; }
      h1:first-of-type { page-break-before: avoid; }
      h2 { font-size: 14pt; margin-top: 1.2em; }
      h3 { font-size: 12pt; }

      /* ── Code blocks ── */
      pre, code { font-size: 9pt; }
      pre {
        background: #f5f5f5;
        border: 1px solid #ddd;
        border-radius: 4px;
        padding: 0.6em 0.8em;
        overflow-x: hidden;
        word-wrap: break-word;
        white-space: pre-wrap;
      }

      /* ── Tables ── */
      table { page-break-inside: avoid; border-collapse: collapse; width: 100%; }
      td, th { padding: 0.3em 0.5em; border: 1px solid #ddd; }
      th { background: #f0f0f0; font-weight: 600; }

      /* ── Images ── */
      img, svg { max-width: 100%; }

      /* ── Page-break hints ── */
      .chapter { page-break-before: always; }
      .chapter:first-child { page-break-before: avoid; }
      h2, h3 { page-break-after: avoid; }

      /* ── Links: show URL in parentheses for external links ── */
      a[href^="http"]::after { content: " (" attr(href) ")"; font-size: 8pt; color: #666; }
      a[href^="http"] { word-break: break-all; }
      /* But not for anchors within the doc */
      a[href^="#"]::after, a[href^="find/"]::after { content: none; }
    </style>
    """

    # The document's own <title> comes from the source page's head (head_html); no
    # project-specific title is hardcoded here, so this script is reusable as-is.
    return (
        "<!DOCTYPE html>\n"
        f'<html lang="en"><head><meta charset="utf-8">\n'
        f"{head_html}\n{pdf_css}\n</head>\n"
        f'<body>\n{"".join(body_parts)}\n</body></html>'
    )


def main() -> None:
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} HTML_INPUT OUTPUT_PDF", file=sys.stderr)
        sys.exit(1)

    html_input = Path(sys.argv[1])
    output_pdf = Path(sys.argv[2])

    try:
        from weasyprint import HTML
    except ImportError:
        print(
            "Error: weasyprint not installed. Install with: pip3 install weasyprint",
            file=sys.stderr,
        )
        sys.exit(1)

    pages = find_all_pages(html_input)
    # Assets (book.css, fonts, the dependency-graph SVG) resolve relative to this dir.
    base_dir = html_input.parent if html_input.is_file() else html_input
    print(f"Found {len(pages)} HTML page(s); base {base_dir}")

    merged = merge_html(pages)

    # Write merged HTML beside the source so weasyprint resolves relative asset paths.
    merged_path = base_dir / "_merged_for_pdf.html"
    merged_path.write_text(merged, encoding="utf-8")

    print(f"Generating PDF: {output_pdf}")
    output_pdf.parent.mkdir(parents=True, exist_ok=True)
    try:
        HTML(filename=str(merged_path), base_url=str(base_dir)).write_pdf(str(output_pdf))
    finally:
        merged_path.unlink(missing_ok=True)
    print(f"PDF generated: {output_pdf} ({output_pdf.stat().st_size / 1024:.0f} KB)")


if __name__ == "__main__":
    main()
