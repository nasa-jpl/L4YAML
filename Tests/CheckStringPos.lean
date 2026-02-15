import Parser

/-!
# String.Pos API exploration

Verify the types available for building a custom `Parser.Stream` instance
in Lean 4.28.0-rc1 with lean4-parser.
-/

-- What is String.Pos in Lean 4.28?
#check @String.Pos
#print String.Pos

-- Raw variant used by lean4-parser
#check @String.Pos.Raw
#print String.Pos.Raw

-- Key operations
#check @String.Pos.Raw.get
#check @String.Pos.Raw.next
#check @String.Pos.Raw.byteIdx

-- Substring.Raw (lean4-parser's standard string stream)
#check @Substring.Raw
#print Substring.Raw

-- Std.Stream instance shape
#check @Std.Stream
#print Std.Stream

-- Parser.Stream class
#check @Parser.Stream
#print Parser.Stream

-- Existing instances for reference
#check @instParserStreamStringSliceChar
#check @instStdStreamStringSliceChar
