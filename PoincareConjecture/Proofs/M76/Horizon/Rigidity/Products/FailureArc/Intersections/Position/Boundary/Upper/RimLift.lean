import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.PeriodicLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimFinitePL
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.AddCircle



set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76.PeriodicSquare

open Dehn
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => unitInterval

theorem SourceSquareMap.exists_finitePL_embedded_rim_lift
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E} {S : Set X}
    (M : SourceSquareMap p K) (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (M.map z))
    (a : V2 → X) (ha : PolyhedralPLInCharts e a Q)
    (haS : MapsTo a Q S) (hai : InjOn a Q) :
    ∃ r : ℝ → P2, FinitePiecewiseAffineOn r (Icc (0 : ℝ) 1) ∧
      (∀ t : I, (h (((r t).1 : AddCircle p), ((r t).2 : AddCircle p)) : X) = a (squareRimLoop t)) ∧
      (∀ s t : I,
        (((r s).1 : AddCircle p), ((r s).2 : AddCircle p)) =
          (((r t).1 : AddCircle p), ((r t).2 : AddCircle p)) ↔
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
      (fun t => (h (((r t).1 : AddCircle p), ((r t).2 : AddCircle p)) : X)) '' Icc (0 : ℝ) 1 =
        a '' Q := by
  let aq : C(Q, S) := ⟨fun z => ⟨a z, haS z.property⟩, ha.continuousOn.domRestrict.subtype_mk _⟩
  let angular : C(I, AddCircle p × AddCircle p) :=
    ⟨fun t => h.symm (aq (squareRimLoop t)), by fun_prop⟩
  obtain ⟨z₀, hz₀⟩ := surjective_projection p (angular 0)
  let angular₀ : C(I, AddCircle p) := ⟨fun t => (angular t).1, by fun_prop⟩
  let angular₁ : C(I, AddCircle p) := ⟨fun t => (angular t).2, by fun_prop⟩
  have hstart₀ : angular₀ 0 = ((z₀.1 : ℝ) : AddCircle p) := (congrArg Prod.fst hz₀).symm
  have hstart₁ : angular₁ 0 = ((z₀.2 : ℝ) : AddCircle p) := (congrArg Prod.snd hz₀).symm
  let cov := AddCircle.isCoveringMap_coe p
  let l₀ := cov.liftPath angular₀ (z₀.1 : ℝ) hstart₀
  let l₁ := cov.liftPath angular₁ (z₀.2 : ℝ) hstart₁
  have hl₀ (t : I) : (l₀ t : AddCircle p) = angular₀ t :=
    congrFun (cov.liftPath_lifts angular₀ (z₀.1 : ℝ) hstart₀) t
  have hl₁ (t : I) : (l₁ t : AddCircle p) = angular₁ t :=
    congrFun (cov.liftPath_lifts angular₁ (z₀.2 : ℝ) hstart₁) t
  let rr : C(I, P2) := ⟨fun t => (l₀ t, l₁ t), by fun_prop⟩
  let r (t : ℝ) : P2 := if ht : t ∈ Icc (0 : ℝ) 1 then rr ⟨t, ht⟩ else 0
  have hrval (t : I) : r t = rr t := by simp only [r, dif_pos t.property]
  have hproject (t : I) :
      (((r t).1 : AddCircle p), ((r t).2 : AddCircle p)) = angular t := by
    rw [hrval]
    exact Prod.ext (hl₀ t) (hl₁ t)
  have hpoint (t : I) :
      (h (((r t).1 : AddCircle p), ((r t).2 : AddCircle p)) : X) = a (squareRimLoop t) := by
    rw [hproject]
    exact congrArg Subtype.val (h.apply_symm_apply _)
  obtain ⟨J, hJ, hJs, hrim⟩ := finitePiecewiseAffineOn_squareRimParameter
  have harim : PolyhedralPLInCharts e (a ∘ squareRimParameter) J.space :=
    ha.comp_finitePiecewiseAffineOn J hJ ⟨J, hJ, rfl, hrim⟩
      (fun t _ => (squareRimLoop.extend t).property)
  have hrc : ContinuousOn r J.space := by
    rw [hJs, continuousOn_iff_continuous_domRestrict]
    exact rr.continuous.congr (fun t => (hrval t).symm)
  have hfr : PolyhedralPLInCharts e
      (fun t => (h (((r t).1 : AddCircle p), ((r t).2 : AddCircle p)) : X)) J.space :=
    harim.congr (fun t ht => by
      change a (squareRimParameter t) = _
      rw [squareRimParameter_apply ⟨t, hJs.subset ht⟩]
      exact (hpoint ⟨t, hJs.subset ht⟩).symm)
  have hrPL := M.finitePiecewiseAffineOn_periodic_lift hcompat H F hF hFval h hvalue J hJ hrc hfr
  refine ⟨r, hJs ▸ hrPL, hpoint, ?_, ?_⟩
  · intro s t
    constructor
    · intro heq
      have heqa : a (squareRimLoop s) = a (squareRimLoop t) :=
        (hpoint s).symm.trans ((congrArg (fun z => (h z : X)) heq).trans (hpoint t))
      exact squareRimLoop_fibers s t (Subtype.ext
        (hai (squareRimLoop s).property (squareRimLoop t).property heqa))
    · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · rw [hproject, hproject]
        change h.symm (aq (squareRimLoop 0)) = h.symm (aq (squareRimLoop 1))
        rw [Path.source, Path.target]
      · rw [hproject, hproject]
        change h.symm (aq (squareRimLoop 1)) = h.symm (aq (squareRimLoop 0))
        rw [Path.source, Path.target]
  · apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨squareRimLoop ⟨t, ht⟩, (squareRimLoop ⟨t, ht⟩).property, (hpoint ⟨t, ht⟩).symm⟩
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨t, ht⟩ := surjective_squareRimLoop ⟨z, hz⟩
      exact ⟨t, t.property, (hpoint t).trans (congrArg a (congrArg Subtype.val ht))⟩

end PoincareConjecture.M76.PeriodicSquare
