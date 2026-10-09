import DihedralHessenberg.Splines.ReflectionGraph

/-! # Injective constant and orbit scalar maps -/

namespace Schubert.Splines.ReflectionGraphData

variable {K S W T : Type*} [CommRing K] [CommRing S] [Algebra K S] [Group W]
variable (data : ReflectionGraphData K S W T)

/-- Evaluation at the group identity makes the constant scalar map injective. -/
theorem constantHom_injective (selected : Set T) :
    Function.Injective (data.constantHom selected) := by
  intro first second heq
  exact congrArg (fun value : data.Spline selected => (value : W → S) 1) heq

/-- Evaluation at the group identity makes the orbit scalar map injective. -/
theorem orbitHom_injective (selected : Set T) :
    Function.Injective (data.orbitHom selected) := by
  intro first second heq
  have hvalue := congrArg (fun value : data.Spline selected => (value : W → S) 1) heq
  change data.action 1 first = data.action 1 second at hvalue
  simpa only [data.action_one_apply] using hvalue

end Schubert.Splines.ReflectionGraphData
