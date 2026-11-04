module

/-!
# The print stylesheet `html-to-pdf` adds to the merged page

The `pdf_css` block of `scripts/html-to-pdf.py`, byte for byte (a raw string: the
leading newline and the trailing four-space indent are part of it).
-/

namespace Scripts.Html

@[expose] public section

def pdfCss : String := r##"
    <style>
      @page {
        size: letter;
        margin: 2cm 1.8cm 2cm 1.8cm;
        @bottom-center { content: counter(page); font-size: 9pt; color: #666; }
        @footnote { border-top: 0.5pt solid #999; padding-top: 6pt; margin-top: 10pt; }
      }

      /* ── Margin notes → footnotes ──
         Verso lays its margin notes (citations included) out entirely under
         `@media screen` and `@container` rules; WeasyPrint renders print media and
         implements no container queries, so without the rules below each note's full
         text flows inline, mid-sentence. WeasyPrint implements CSS-GCPM footnotes,
         so the print form of a margin note is a numbered footnote at the bottom of
         its page (the @footnote area above draws the separator rule). */
      .marginalia .note { float: footnote; font-size: 9pt; line-height: 1.4; }
      /* Footnotes bring their own call mark and marker, so the screen design's
         CSS-counter pair (superscript mark in the text, number on the note) is
         suppressed in print. */
      .marginalia::after { content: none !important; }
      .marginalia .note::before { content: none !important; }
      .marginalia .note::footnote-call {
        content: counter(footnote);
        vertical-align: super;
        font-size: 0.7em;
        font-weight: bold;
      }
      .marginalia .note::footnote-marker {
        content: counter(footnote) ". ";
        font-weight: bold;
      }

      /* ── Hide web-only chrome ──
         The chrome / declaration-body / dashboard subtrees that pollute the outline
         are removed *structurally* by the Python post-processor (BodyExtractor); the
         rules below are a visual fallback for anything left in the body that should
         not print but carries no heading (so it never reaches the bookmark outline).
         Note: CSS display:none alone does NOT suffice for the outline — WeasyPrint
         still emits PDF bookmarks for hidden headings, which is why the offending
         elements are pruned from the DOM rather than only hidden here. */
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
      .bp_external_decl_body,
      pre.docstring,
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
    "##

end

end Scripts.Html
