(module iface-test mzscheme
  (require "iface-checker.scm")
  (require (planet "test.ss" ("schematics" "schemeunit.plt" 1 1)))
  (require (planet "graphical-ui.ss" ("schematics" "schemeunit.plt" 1 1)))
  
  (define empty-class "class C {}")
  
  (define simple-class "import java.util ; class C{int x;java.lang.Object y;Vector z;}")

  
  
  )