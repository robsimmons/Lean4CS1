import VersoManual
import FPCourse
open Verso.Genre.Manual
def main := manualMain (%doc FPCourse) (config := {
  htmlDepth := 2
  rootTocDepth := .some 2
  sectionTocDepth := .some 2
  
})
