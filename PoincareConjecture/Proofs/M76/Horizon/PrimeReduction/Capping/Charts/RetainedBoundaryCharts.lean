import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.RetainedModelNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.FinitePLCarrierChartCompatibility
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.OpenCarrierChartRestriction
import PoincareConjecture.Proofs.M76.Mathlib.CompatibleChartPLMaps
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_chart_on_open_model_image
    {X Y V : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace V]
    {U : Set X} {W : Set Y} (f : X → Y) (G : U ≃ₜ f '' U)
    (hG : ∀ x : U, (G x : Y) = f x) (hU : IsOpen U)
    (hUW : f '' U ⊆ W)
    (hopen : IsOpen ((Subtype.val : W → Y) ⁻¹' (f '' U)))
    (B : OpenPartialHomeomorph X V) (p : U) (hp : (p : X) ∈ B.source) :
    ∃ q : OpenPartialHomeomorph W V,
      q.source = (Subtype.val : W → Y) ⁻¹' (f '' (U ∩ B.source)) ∧
      q.target = B.target ∩ B.symm ⁻¹' U ∧
      (⟨f p, hUW (mem_image_of_mem f p.property)⟩ : W) ∈ q.source ∧
      (∀ x : U, (x : X) ∈ B.source →
        q ⟨f x, hUW (mem_image_of_mem f x.property)⟩ = B x) ∧
      ∀ y ∈ q.target, (q.symm y : Y) = f (B.symm y) := by
  let O : TopologicalSpace.Opens W := ⟨(Subtype.val : W → Y) ⁻¹' (f '' U), hopen⟩
  let J : (f '' U) ≃ₜ O := {
    toFun := fun x => ⟨⟨x, hUW x.property⟩, x.property⟩
    invFun := fun x => ⟨(x : W), x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let hO : Nonempty O := ⟨J (G p)⟩
  let H := G.trans J
  let j := H.toOpenPartialHomeomorph.trans (O.openPartialHomeomorphSubtypeCoe hO)
  have hjs : j.source = Set.univ := by simp [j]
  have hjt : j.target = (Subtype.val : W → Y) ⁻¹' (f '' U) := by simp [j, O]
  have hjv (x : U) : (j x : Y) = f x := hG x
  let Uo : TopologicalSpace.Opens X := ⟨U, hU⟩
  let hUn : Nonempty Uo := ⟨p⟩
  let Br := B.subtypeRestr hUn
  let q := j.symm.trans Br
  have hqs : q.source = (Subtype.val : W → Y) ⁻¹' (f '' (U ∩ B.source)) := by
    ext z
    constructor
    · rintro ⟨hz, hzB⟩
      have hz' : z ∈ j.target := hz
      rw [hjt] at hz'
      obtain ⟨x, hxU, hfx⟩ := hz'
      have hxj : j ⟨x, hxU⟩ = z := Subtype.ext ((hjv _).trans hfx)
      have hxinv : j.symm z = ⟨x, hxU⟩ := by
        rw [← hxj]
        exact j.left_inv (hjs.symm ▸ mem_univ _)
      change j.symm z ∈ Br.source at hzB
      rw [hxinv, B.subtypeRestr_source hUn] at hzB
      exact ⟨x, ⟨hxU, hzB⟩, hfx⟩
    · rintro ⟨x, ⟨hxU, hxB⟩, hfx⟩
      have hxj : j ⟨x, hxU⟩ = z := Subtype.ext ((hjv _).trans hfx)
      have hxinv : j.symm z = ⟨x, hxU⟩ := by
        rw [← hxj]
        exact j.left_inv (hjs.symm ▸ mem_univ _)
      refine ⟨?_, ?_⟩
      · change z ∈ j.target
        rw [hjt]
        exact ⟨x, hxU, hfx⟩
      · change j.symm z ∈ Br.source
        rw [hxinv, B.subtypeRestr_source hUn]
        exact hxB
  have hqt : q.target = B.target ∩ B.symm ⁻¹' U := by
    change Br.target ∩ Br.symm ⁻¹' j.source = _
    rw [hjs]
    simp only [preimage_univ, inter_univ]
    simp only [Br, OpenPartialHomeomorph.subtypeRestr_def,
      OpenPartialHomeomorph.trans_target,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    rfl
  refine ⟨q, hqs, hqt, ?_, ?_, ?_⟩
  · rw [hqs]
    exact ⟨p, ⟨p.property, hp⟩, rfl⟩
  · intro x hx
    change Br (j.symm ⟨f x, _⟩) = B x
    have hxj : j x = ⟨f x, hUW (mem_image_of_mem f x.property)⟩ := Subtype.ext (hjv x)
    rw [← hxj, j.left_inv (hjs.symm ▸ mem_univ _)]
    rfl
  · intro y hy
    have hyBr : y ∈ Br.target := hy.1
    change (j (Br.symm y) : Y) = _
    rw [hjv]
    exact congrArg f (B.subtypeRestr_symm_apply hUn hyBr)

theorem exists_retained_original_chart
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X} {P C : Set E}
    (he : PLDomain e R) (H : R ≃ₜ P) (f : X → E)
    (hH : ∀ x : R, (H x : E) = f x)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hUR : U ⊆ R) (hU : IsOpen U) (hP : IsClosed P) (hC : IsClosed C)
    (hdis : Disjoint (f '' U) C)
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (p : U) (hp : (p : X) ∈ B.source) :
    ∃ (hUW : f '' U ⊆ P ∪ C) (q : OpenPartialHomeomorph ↥(P ∪ C) V3),
      q.source = (Subtype.val : ↥(P ∪ C) → E) ⁻¹' (f '' (U ∩ B.source)) ∧
      q.target = B.target ∩ B.symm ⁻¹' U ∧
      (⟨f p, hUW (mem_image_of_mem f p.property)⟩ : ↥(P ∪ C)) ∈ q.source ∧
      (∀ x : U, (x : X) ∈ B.source →
        q ⟨f x, hUW (mem_image_of_mem f x.property)⟩ = B x) ∧
      (∀ y ∈ q.target, (q.symm y : E) = f (B.symm y)) ∧
      LocallyPiecewiseAffineOn (fun y => (q.symm y : E)) q.target := by
  obtain ⟨G, hG, hUW, hopen⟩ :=
    exists_retained_open_model_homeomorph H f hH hUR hU hP hC hdis
  obtain ⟨q, hqs, hqt, hpq, hqf, hqg⟩ :=
    exists_chart_on_open_model_image f G hG hU hUW hopen B p hp
  refine ⟨hUW, q, hqs, hqt, hpq, hqf, hqg, ?_⟩
  have hlocal := OpenPartialHomeomorph.locallyPiecewiseAffineOn_compatible_chart
    e he.cover hf B hB
  apply (hlocal.mono q.open_target (hqt.subset.trans inter_subset_left)).congr
  exact fun y hy => (hqg y hy).symm

theorem retained_chart_capped_halfspace_eq
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {R U D : Set X} {W C : Set E} (f : X → E)
    (hfi : InjOn f R) (hUR : U ⊆ R) (hDR : D ⊆ R)
    (hdis : Disjoint (f '' U) C)
    (B : OpenPartialHomeomorph X V3) (q : OpenPartialHomeomorph W V3)
    (hqt : q.target ⊆ B.target ∩ B.symm ⁻¹' U)
    (hqg : ∀ y ∈ q.target, (q.symm y : E) = f (B.symm y))
    (ell : V3 → ℝ)
    (hregion : ∀ x ∈ U ∩ B.source, x ∈ D ↔ 0 ≤ ell (B x)) :
    ∀ z ∈ q.source, (z : E) ∈ f '' D ∪ C ↔ 0 ≤ ell (q z) := by
  intro z hz
  have hy := hqt (q.mapsTo hz)
  let x := B.symm (q z)
  have hxU : x ∈ U := hy.2
  have hxB : x ∈ B.source := B.symm.mapsTo hy.1
  have hfx : f x = (z : E) :=
    (hqg (q z) (q.mapsTo hz)).symm.trans (congrArg Subtype.val (q.left_inv hz))
  have hzC : (z : E) ∉ C := by
    intro hzC
    exact disjoint_left.mp hdis ⟨x, hxU, hfx⟩ hzC
  have hmem : (z : E) ∈ f '' D ↔ x ∈ D := by
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hwx := hfi (hDR hw) (hUR hxU) (hwz.trans hfx.symm)
      exact hwx ▸ hw
    · intro hxD
      exact ⟨x, hxD, hfx⟩
  rw [mem_union, or_iff_left hzC, hmem, hregion x ⟨hxU, hxB⟩]
  rw [show B x = q z from B.right_inv hy.1]

theorem exists_retained_boundary_halfspace_chart
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R U D : Set X} {P C : Set E}
    (he : PLDomain e R) (hD : PLDomain e D) (hDR : D ⊆ R)
    (H : R ≃ₜ P) (f : X → E) (hH : ∀ x : R, (H x : E) = f x)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hUR : U ⊆ R) (hU : IsOpen U) (hP : IsClosed P) (hC : IsClosed C)
    (hdis : Disjoint (f '' U) C) (p : U) (hp : (p : X) ∈ frontier D) :
    ∃ (hpW : f p ∈ P ∪ C) (q : OpenPartialHomeomorph ↥(P ∪ C) V3)
      (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ (⟨f p, hpW⟩ : ↥(P ∪ C)) ∈ q.source ∧
      ell (q ⟨f p, hpW⟩) = 0 ∧
      (∀ z ∈ q.source, (z : E) ∈ f '' D ∪ C ↔ 0 ≤ ell (q z)) ∧
      LocallyPiecewiseAffineOn (fun y => (q.symm y : E)) q.target ∧
      ∀ z ∈ q.source, (z : E) ∈ f '' U := by
  obtain ⟨ell, v, B, hell, hpB, hzero, hB, hregion⟩ := hD.halfspace p hp
  obtain ⟨hUW, q, hqs, hqt, hpq, hqf, hqg, hlocal⟩ :=
    exists_retained_original_chart he H f hH hf hUR hU hP hC hdis B hB p hpB
  have hfi : InjOn f R := by
    intro x hx y hy hxy
    have hxyH : H ⟨x, hx⟩ = H ⟨y, hy⟩ :=
      Subtype.ext ((hH ⟨x, hx⟩).trans (hxy.trans (hH ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective hxyH)
  refine ⟨hUW (mem_image_of_mem f p.property), q, ell, v, hell, hpq, ?_, ?_, hlocal, ?_⟩
  · rw [hqf p hpB]
    exact hzero
  · exact retained_chart_capped_halfspace_eq f hfi hUR hDR hdis B q hqt.subset hqg ell
      (fun x hx => hregion x hx.2)
  · intro z hz
    rw [hqs] at hz
    exact image_mono inter_subset_left hz

theorem exists_open_carrier_halfspace_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T W D : Set E} (hWT : W ⊆ T)
    (hW : IsOpen ((Subtype.val : T → E) ⁻¹' W))
    (q : OpenPartialHomeomorph T V3) (ell : V3 → ℝ)
    (p : W) (hp : (⟨p, hWT p.property⟩ : T) ∈ q.source)
    (hzero : ell (q ⟨p, hWT p.property⟩) = 0)
    (hregion : ∀ z ∈ q.source, (z : E) ∈ D ↔ 0 ≤ ell (q z))
    (hlocal : LocallyPiecewiseAffineOn (fun y => (q.symm y : E)) q.target) :
    ∃ B : OpenPartialHomeomorph W V3,
      p ∈ B.source ∧ ell (B p) = 0 ∧
      (∀ z ∈ B.source, (z : E) ∈ D ↔ 0 ≤ ell (B z)) ∧
      LocallyPiecewiseAffineOn (fun y => (B.symm y : E)) B.target := by
  obtain ⟨B, hBs, hBt, hpB, hBf, hBg⟩ :=
    OpenPartialHomeomorph.exists_open_carrier_restriction hWT hW q p hp
  refine ⟨B, hpB, ?_, ?_, ?_⟩
  · rw [hBf]
    exact hzero
  · intro z hz
    rw [hBf]
    rw [hBs] at hz
    exact hregion ⟨z, hWT z.property⟩ hz
  · apply (hlocal.mono B.open_target (hBt.subset.trans inter_subset_left)).congr
    exact fun y hy => (hBg y hy).symm

end PoincareConjecture.M76

namespace OpenPartialHomeomorph

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem mem_piecewiseAffineGroupoid_transition_of_locallyPL_inverse
    {W : Set E} (Q Q' : OpenPartialHomeomorph W V)
    (hQ : LocallyPiecewiseAffineOn (fun y => (Q.symm y : E)) Q.target)
    {A : Set E} {f : E → V} (hf : FinitePiecewiseAffineOn f A)
    (hQs : ∀ x ∈ Q'.source, (x : E) ∈ A)
    (hQf : ∀ x ∈ Q'.source, Q' x = f x) :
    Q.symm.trans Q' ∈ piecewiseAffineGroupoid V := by
  obtain ⟨f', U, _, hAU, hf', hff⟩ := hf.exists_locallyPiecewiseAffine_extension
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  have hcomp : LocallyPiecewiseAffineOn
      (f' ∘ fun y => (Q.symm y : E)) (Q.symm.trans Q').source := by
    apply (hf'.comp hQ).mono (Q.symm.trans Q').open_source
    intro y hy
    exact ⟨hy.1, hAU (hQs (Q.symm y) hy.2)⟩
  apply hcomp.congr
  intro y hy
  have hy' : Q.symm y ∈ Q'.source := hy.2
  exact (hff (hQs (Q.symm y) hy')).trans (hQf (Q.symm y) hy').symm

end OpenPartialHomeomorph
