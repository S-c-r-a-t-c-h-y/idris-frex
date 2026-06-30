module Main

import Test.Golden

%default covering

tests : TestPool
tests = MkTestPool "Frex tests" [] Nothing
  ["distributive-combinations"]
-- tests = MkTestPool "Frex tests" [] Nothing
--   [ "monoids"
--   , "commutative-monoids"
--   , "printer"
--   , "certificates"
--   , "involutive-monoids"
--   , "indexed-binary"
--   , "distributive-combinations"
--   ]

main : IO ()
main = runner [ { testCases $= map ("frextests/" ++) } tests ]
