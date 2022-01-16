import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Sources
import Prolala.Federal.Civpro.Pleading.Defs
import Prolala.Federal.Civpro.Defs

open Time Us.Federal

inductive Pretrial.Step where
deriving DecidableEq, Repr

inductive Pretrial.WfStep : Civpro.State -> Step -> Civpro.State -> Prop
