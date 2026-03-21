import VersoManual
import FPCourse
open Verso.Genre.Manual
def main := manualMain (%doc FPCourse) (config := {
  htmlDepth := 1
  rootTocDepth := .some 1
  sectionTocDepth := .some 1
})
