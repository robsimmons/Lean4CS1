-- FPCourse.lean — library root; imports all 14 weekly modules

import VersoManual

import FPCourse.Unit1.Week00_AlgebraicTypes
import FPCourse.Unit1.Week01_ExpressionsTypesValues
import FPCourse.Unit1.Week02_FunctionsSpecifications
import FPCourse.Unit1.Week03_RecursionTermination

import FPCourse.Unit2.Week04_AlgebraicDatatypes
import FPCourse.Unit2.Week05_Lists
import FPCourse.Unit2.Week06_Trees
import FPCourse.Unit2.Week07_PolymorphismDecidability

import FPCourse.Unit3.Week08_HigherOrderFunctions
import FPCourse.Unit3.Week09_Specifications

import FPCourse.Unit4.Week10_SetsRelations

import FPCourse.Unit5.Week11_AbstractTypes
import FPCourse.Unit5.Week12_TypeClassesDecidable

import FPCourse.Unit6.Week14_CurryHoward

open Verso.Genre Manual
open Week00
open Week01
open Week02
open Week03
open Week04

#doc (Manual) "CS1: Programming, Certified" =>

A forked [Verso](https://verso.lean-lang.org) translation of the course by
Kevin Sullivan, [available on GitHub](https://github.com/kevinsullivan/Lean4CS1).
See [kevinsullivan.github.io/Lean4CS1](https://kevinsullivan.github.io/Lean4CS1/)
for the official version.

{include FPCourse.Unit1.Week00_AlgebraicTypes}
{include FPCourse.Unit1.Week01_ExpressionsTypesValues}
{include FPCourse.Unit1.Week02_FunctionsSpecifications}
{include FPCourse.Unit1.Week03_RecursionTermination}
{include FPCourse.Unit2.Week04_AlgebraicDatatypes}
