import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Sources
import Prolala.Federal.Civpro.Enforcement.Defs
import Prolala.Federal.Civpro.Defs

open Time
inductive Enforcement.Step where
deriving DecidableEq, Repr

inductive Enforcement.WfStep : Civpro.State -> Step -> Civpro.State -> Prop
