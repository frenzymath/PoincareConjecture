import PoincareConjecture.Proofs.M76.Dehn.PLDomainMarkedApproximation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.AnnulusProjection
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

open Dehn Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem exists_marked_PL_annulus_pair
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    (F : Bool → Set X) (hF : ∀ b, F b ⊆ frontier R)
    (hFclopen : ∀ b, IsClopen ((Subtype.val : frontier R → X) ⁻¹' F b))
    (f : C(source, R)) (gamma : ∀ b, C(Q2, F b))
    (hpair : ∀ (b : Bool) (u : Q2),
      (f ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩ : X) =
        (gamma b u : X)) :
    ∃ (g : (V1 × V2) → X) (a : C(source, R)),
      PolyhedralPLInCharts e g source ∧ (∀ x : source, g x = (a x : X)) ∧
      ∃ gamma₀ : ∀ b, C(Q2, F b),
        (∀ (b : Bool) (u : Q2), g (endpoint b, u) = (gamma₀ b u : X)) ∧
        ∀ b, Nonempty ((gamma b).Homotopy (gamma₀ b)) := by
  classical
  obtain ⟨K, hK, hKs⟩ := exists_source_triangulation
  let : CompactSpace source := isCompact_iff_compactSpace.mp
    (hKs ▸ K.isCompact_space_of_finite hK)
  let inc (b : Bool) : C(Q2, source) :=
    ⟨fun u => ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩,
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩
  let B : Set source := {x | (x : V1 × V2).1 ∈ sphere (0 : V1) 1}
  have hB : IsCompact B :=
    (isClosed_sphere.preimage (continuous_fst.comp continuous_subtype_val)).isCompact
  have hBF : MapsTo (fun x : source => (f x : X)) B (F false ∪ F true) := by
    intro x hx
    obtain ⟨b, hb⟩ := (mem_sphere_iff_exists_endpoint (x : V1 × V2).1).mp hx
    let u : Q2 := ⟨(x : V1 × V2).2, x.property.2⟩
    have hxinc : x = inc b u := Subtype.ext (Prod.ext hb rfl)
    rw [hxinc]
    change (f (inc b u) : X) ∈ F false ∪ F true
    rw [show (f (inc b u) : X) = (gamma b u : X) from hpair b u]
    cases b
    · exact Or.inl (gamma false u).property
    · exact Or.inr (gamma true u).property
  obtain ⟨g, a, hg, hga, H, hH⟩ := he.exists_marked_PL_approximation
    source ⟨K, hK, hKs⟩ (inc false squareRimBase) f B hB (F false ∪ F true)
    (union_subset (hF false) (hF true))
    ((hFclopen false).isOpen.union (hFclopen true).isOpen) hBF
  have hstay (b : Bool) (u : Q2) (t : unitInterval) : (H (t, inc b u) : X) ∈ F b := by
    have hfront (s : unitInterval) : (H (s, inc b u) : X) ∈ frontier R :=
      (union_subset (hF false) (hF true))
        (hH s (inc b u) (endpoint_mem_sphere b))
    let trace : C(unitInterval, frontier R) :=
      ⟨fun s => ⟨H (s, inc b u), hfront s⟩,
        (continuous_subtype_val.comp
          (H.continuous.comp (continuous_id.prodMk continuous_const))).subtype_mk _⟩
    have hzero : trace 0 ∈ (Subtype.val : frontier R → X) ⁻¹' F b := by
      change (H (0, inc b u) : X) ∈ F b
      rw [H.apply_zero]
      rw [show (f (inc b u) : X) = (gamma b u : X) from hpair b u]
      exact (gamma b u).property
    have hall := ((hFclopen b).preimage trace.continuous).eq_univ ⟨0, hzero⟩
    exact (show t ∈ trace ⁻¹' ((Subtype.val : frontier R → X) ⁻¹' F b) from
      hall.symm ▸ mem_univ t)
  have haF (b : Bool) (u : Q2) : (a (inc b u) : X) ∈ F b := by
    simpa only [H.apply_one] using hstay b u 1
  let gamma₀ (b : Bool) : C(Q2, F b) :=
    ⟨fun u => ⟨a (inc b u), haF b u⟩,
      (continuous_subtype_val.comp (a.continuous.comp (inc b).continuous)).subtype_mk _⟩
  refine ⟨g, a, hg, hga, gamma₀, ?_, ?_⟩
  · intro b u
    exact hga (inc b u)
  · intro b
    refine ⟨{
      toFun := fun z => ⟨H (z.1, inc b z.2), hstay b z.2 z.1⟩
      continuous_toFun := (continuous_subtype_val.comp
        (H.continuous.comp (continuous_fst.prodMk
          ((inc b).continuous.comp continuous_snd)))).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro u
      apply Subtype.ext
      change (H (0, inc b u) : X) = (gamma b u : X)
      rw [H.apply_zero]
      exact hpair b u
    · intro u
      apply Subtype.ext
      exact congrArg (fun x : R => (x : X)) (H.apply_one (inc b u))

end PoincareConjecture.M76
