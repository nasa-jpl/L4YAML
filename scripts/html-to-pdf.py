#!/usr/bin/env python3
"""Convert the Verso HTML site to a single PDF document.

Usage: python3 scripts/html-to-pdf.py HTML_DIR OUTPUT_PDF

Requires: weasyprint (pip3 install weasyprint)
"""
import sys
from pathlib import Path


def find_all_pages(html_dir: Path) -> list[Path]:
    """Discover all index.html files in the Verso output tree, ordered for PDF."""
    root_index = html_dir / "index.html"
    if not root_index.is_file():
        print(f"Error: {root_index} not found", file=sys.stderr)
        sys.exit(1)

    pages = [root_index]
    # Verso with htmlDepth=2 creates subdirectories for each chapter
    for child in sorted(html_dir.iterdir()):
        if child.is_dir():
            sub_index = child / "index.html"
            if sub_index.is_file():
                pages.append(sub_index)
            # Check one level deeper for subsections
            for grandchild in sorted(child.iterdir()):
                if grandchild.is_dir():
                    sub_sub = grandchild / "index.html"
                    if sub_sub.is_file():
                        pages.append(sub_sub)
    return pages


def merge_html(pages: list[Path], html_dir: Path) -> str:
    """Create a single HTML document from multiple pages for PDF rendering."""
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
      @page { size: letter; margin: 2cm; }
      body { font-family: system-ui, -apple-system, sans-serif; font-size: 11pt; }
      h1 { page-break-before: always; }
      h1:first-of-type { page-break-before: avoid; }
      pre, code { font-size: 9pt; }
      table { page-break-inside: avoid; }
      img { max-width: 100%; }
      nav, .nav-sidebar, .breadcrumb { display: none; }
    </style>
    """

    return (
        "<!DOCTYPE html>\n"
        f'<html lang="en"><head><meta charset="utf-8">\n'
        f"<title>L4YAML Documentation</title>\n"
        f"{head_html}\n{pdf_css}\n</head>\n"
        f'<body>\n{"".join(body_parts)}\n</body></html>'
    )


def main() -> None:
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} HTML_DIR OUTPUT_PDF", file=sys.stderr)
        sys.exit(1)

    html_dir = Path(sys.argv[1])
    output_pdf = Path(sys.argv[2])

    try:
        from weasyprint import HTML
    except ImportError:
        print(
            "Error: weasyprint not installed. Install with: pip3 install weasyprint",
            file=sys.stderr,
        )
        sys.exit(1)

    pages = find_all_pages(html_dir)
    print(f"Found {len(pages)} HTML pages in {html_dir}")

    merged = merge_html(pages, html_dir)

    # Write merged HTML to a temp file for weasyprint (needed for relative paths)
    merged_path = html_dir / "_merged_for_pdf.html"
    merged_path.write_text(merged, encoding="utf-8")

    print(f"Generating PDF: {output_pdf}")
    output_pdf.parent.mkdir(parents=True, exist_ok=True)
    HTML(filename=str(merged_path), base_url=str(html_dir)).write_pdf(str(output_pdf))
    merged_path.unlink()
    print(f"PDF generated: {output_pdf} ({output_pdf.stat().st_size / 1024:.0f} KB)")


if __name__ == "__main__":
    main()
