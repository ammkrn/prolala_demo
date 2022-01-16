import Prolala.Federal.Civpro.Jurisdiction.Diversity

structure FederalQuestion where
  questionCitation : String
  explanation : String
deriving DecidableEq, Repr

inductive Personal
| inPersonam
| inRem
| quasiInRem
deriving DecidableEq, Repr

inductive Jurisdiction.SubjectMatter
| federalQuestion : FederalQuestion → SubjectMatter
| diversity : DiversityResult → SubjectMatter
| classActionFairness (statement : String) : SubjectMatter
| supplemental (supplementingCaseNum : Nat) : SubjectMatter

