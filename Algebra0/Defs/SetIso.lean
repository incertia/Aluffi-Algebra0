import Mathlib.Logic.Function.Basic

def SetIso (α : Type) (β : Type) : Prop := ∃f : α → β, Function.Bijective f
