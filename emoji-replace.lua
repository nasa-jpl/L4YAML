-- Pandoc Lua filter: replace emoji with LaTeX-safe text symbols
function Str(elem)
  elem.text = elem.text:gsub("✅", "PASS")
  elem.text = elem.text:gsub("❌", "FAIL")
  return elem
end
