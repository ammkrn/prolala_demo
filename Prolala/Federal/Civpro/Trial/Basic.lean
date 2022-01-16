import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Sources
--import Prolala.Federal.Civpro.Pleading.Info
import Prolala.Federal.Civpro.Trial.Defs
import Prolala.Federal.Civpro.Defs
--import Prolala.Federal.Civpro.Pleading.Complaint

open Time
inductive Trial.Step where
deriving DecidableEq, Repr


inductive Trial.WfStep : Civpro.State -> Step -> Civpro.State -> Prop
