import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Iteration.TerminalAnnuli
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse










set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))



theorem exists_finitePL_annulus_inverse_coordinates
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {P : Set X} (A : Ann ≃ₜ P) (q : P2 → X)
    (hq : PolyhedralPLInCharts e q Ann) (hA : ∀ z : Ann, (A z : X) = q z)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (r : E → X) (hr : PolyhedralPLInCharts e r K.space)
    (hrP : MapsTo r K.space P) :
    ∃ lift : E → P2, FinitePiecewiseAffineOn lift K.space ∧
      MapsTo lift K.space Ann ∧
      (∀ x : K.space, lift x = (A.symm ⟨r x, hrP x.property⟩ : P2)) ∧
      ∀ x ∈ K.space, q (lift x) = r x := by
  classical
  let lift : E → P2 := fun x =>
    if hx : x ∈ K.space then (A.symm ⟨r x, hrP hx⟩ : P2) else 0
  have hval (x : E) (hx : x ∈ K.space) :
      lift x = (A.symm ⟨r x, hrP hx⟩ : P2) := by simp only [lift, dif_pos hx]
  have hlift : ContinuousOn lift K.space := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun x : K.space =>
        (A.symm ⟨r x, hrP x.property⟩ : P2)) :=
      continuous_subtype_val.comp (A.symm.continuous.comp (hr.continuousOn.domRestrict.subtype_mk _))
    exact hc.congr (fun x => (hval x x.property).symm)
  have hmap : MapsTo lift K.space Ann := by
    intro x hx
    rw [hval x hx]
    exact (A.symm ⟨r x, hrP hx⟩).property
  have hcomp (x : E) (hx : x ∈ K.space) : q (lift x) = r x := by
    rw [hval x hx, ← hA]
    exact congrArg Subtype.val (A.apply_symm_apply ⟨r x, hrP hx⟩)
  have hqi : InjOn q Ann := by
    intro x hx y hy heq
    have hh : A ⟨x, hx⟩ = A ⟨y, hy⟩ := by
      apply Subtype.ext
      exact (hA ⟨x, hx⟩).trans (heq.trans (hA ⟨y, hy⟩).symm)
    exact congrArg Subtype.val (A.injective hh)
  refine ⟨lift, ?_, hmap, fun x => hval x x.property, hcomp⟩
  exact hq.finitePiecewiseAffineOn_lift hcompat hqi K hK hlift hmap
    (hr.congr (fun x hx => (hcomp x hx).symm))



theorem polyhedralPL_annulus_transition_on_parameter
    {E X Y ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3} {d : κ → OpenPartialHomeomorph Y V3}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {P : Set X} {Q : Set Y} (A : Ann ≃ₜ P) (A' : Ann ≃ₜ Q)
    (q : P2 → X) (q' : P2 → Y)
    (hq : PolyhedralPLInCharts e q Ann) (hA : ∀ z : Ann, (A z : X) = q z)
    (hq' : PolyhedralPLInCharts d q' Ann) (hA' : ∀ z : Ann, (A' z : Y) = q' z)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (r : E → X) (hr : PolyhedralPLInCharts e r K.space) (hrP : MapsTo r K.space P)
    (f : E → Y)
    (hf : ∀ x : K.space, f x = ((A.symm.trans A') ⟨r x, hrP x.property⟩ : Y)) :
    PolyhedralPLInCharts d f K.space := by
  obtain ⟨lift, hlift, hmap, hval, _⟩ :=
    exists_finitePL_annulus_inverse_coordinates hcompat A q hq hA K hK r hr hrP
  apply (hq'.comp_finitePiecewiseAffineOn K hK hlift hmap).congr
  intro x hx
  change q' (lift x) = f x
  rw [hval ⟨x, hx⟩, hf ⟨x, hx⟩]
  exact (hA' (A.symm ⟨r x, hrP hx⟩)).symm



theorem exists_polyhedralPL_annulus_precomposition
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {P : Set X}
    (A : Ann ≃ₜ P) (q : P2 → X)
    (hq : PolyhedralPLInCharts e q Ann) (hA : ∀ z : Ann, (A z : X) = q z)
    (twist : Ann ≃ₜ Ann) (htwist : twist.IsFinitePL) :
    ∃ qtwist : P2 → X, PolyhedralPLInCharts e qtwist Ann ∧
      ∀ z : Ann, ((twist.trans A) z : X) = qtwist z := by
  obtain ⟨f, hf, hfval⟩ := htwist
  obtain ⟨K, hK, hKs, hfaces⟩ := hf
  have hmap : MapsTo f K.space Ann := by
    intro x hx
    have hxAnn : x ∈ Ann := hKs.subset hx
    rw [← hfval ⟨x, hxAnn⟩]
    exact (twist ⟨x, hxAnn⟩).property
  have hPL : PolyhedralPLInCharts e (q ∘ f) Ann :=
    hKs ▸ hq.comp_finitePiecewiseAffineOn K hK (hfaces.finitePiecewiseAffineOn hK) hmap
  refine ⟨q ∘ f, hPL, ?_⟩
  intro z
  change (A (twist z) : X) = q (f z)
  rw [hA, ← hfval z]



theorem annulus_transition_rim_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {P : Set X} {Q : Set Y} (A : Ann ≃ₜ P) (A' : Ann ≃ₜ Q)
    (sourceRim : Bool → Circle → P) (targetRim : Bool → Circle → Q)
    (hsource : ∀ side z, A (Dehn.annulusRimPoint side z) = sourceRim side z)
    (htarget : ∀ side z, A' (Dehn.annulusRimPoint side z) = targetRim side z) :
    ∀ side z, (A.symm.trans A') (sourceRim side z) = targetRim side z := by
  intro side z
  change A' (A.symm (sourceRim side z)) = targetRim side z
  rw [← hsource, A.symm_apply_apply, htarget]

end PoincareConjecture.M76.HamiltonIntervalTorus
