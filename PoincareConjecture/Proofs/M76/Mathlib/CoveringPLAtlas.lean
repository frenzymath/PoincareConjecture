import PoincareConjecture.Proofs.M76.Mathlib.ImmersionPLAtlas
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts











set_option autoImplicit false

open Set Geometry

namespace IsLocalHomeomorph






theorem exists_piecewiseAffine_coordinate_cover_over
    {X M E ι : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {p : X → M} (hp : IsLocalHomeomorph p)
    (c : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ y, ∃ i, y ∈ (c i).source)
    (hcompat : ∀ i j, (c i).symm.trans (c j) ∈ piecewiseAffineGroupoid E) :
    ∃ d : ι × X → OpenPartialHomeomorph X E,
      (∀ x, ∃ k, x ∈ (d k).source) ∧
      (∀ i x, x ∈ (d (i, x)).source ↔ p x ∈ (c i).source) ∧
      (∀ k, MapsTo p (d k).source (c k.1).source) ∧
      (∀ k, (d k).target ⊆ (c k.1).target) ∧
      (∀ k, (d k : X → E) = (c k.1) ∘ p) ∧
      (∀ k, EqOn (p ∘ (d k).symm) (c k.1).symm (d k).target) ∧
      ∀ k l, (d k).symm.trans (d l) ∈ piecewiseAffineGroupoid E := by
  let d : ι × X → OpenPartialHomeomorph X E :=
    fun k => (hp.localInverseAt k.2).symm.trans (c k.1)
  have hval (k : ι × X) : (d k : X → E) = (c k.1) ∘ p := by
    funext x
    change c k.1 ((hp.localInverseAt k.2).symm x) = c k.1 (p x)
    rw [hp.localInverseAt_symm]
  have hsource (k : ι × X) : MapsTo p (d k).source (c k.1).source := by
    intro x hx
    change x ∈ (hp.localInverseAt k.2).target ∧
      (hp.localInverseAt k.2).symm x ∈ (c k.1).source at hx
    simpa only [hp.localInverseAt_symm] using hx.2
  have htarget (k : ι × X) : (d k).target ⊆ (c k.1).target := fun _ hx => hx.1
  have hinv (k : ι × X) :
      EqOn (p ∘ (d k).symm) (c k.1).symm (d k).target := by
    intro y hy
    exact hp.apply_localInverseAt_of_mem hy.2
  have hcenter (i : ι) (x : X) :
      x ∈ (d (i, x)).source ↔ p x ∈ (c i).source := by
    change (x ∈ (hp.localInverseAt x).target ∧
      (hp.localInverseAt x).symm x ∈ (c i).source) ↔ _
    simp only [hp.self_mem_localInverseAt_target, hp.localInverseAt_symm, true_and]
  refine ⟨d, ?_, hcenter, hsource, htarget, hval, hinv, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := hcover (p x)
    exact ⟨(i, x), (hcenter i x).mpr hi⟩
  · intro k l
    have hsub : ((d k).symm.trans (d l)).source ⊆
        ((c k.1).symm.trans (c l.1)).source := by
      intro y hy
      refine ⟨htarget k hy.1, ?_⟩
      have h := hsource l hy.2
      have he : p ((d k).symm y) = (c k.1).symm y := hinv k hy.1
      change p ((d k).symm y) ∈ (c l.1).source at h
      change (c k.1).symm y ∈ (c l.1).source
      exact he ▸ h
    have heq : EqOn ((d k).symm.trans (d l))
        ((c k.1).symm.trans (c l.1)) ((d k).symm.trans (d l)).source := by
      intro y hy
      change d l ((d k).symm y) = c l.1 ((c k.1).symm y)
      rw [hval l]
      exact congrArg (c l.1) (hinv k hy.1)
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact (((mem_piecewiseAffineGroupoid_iff_forward _).mp (hcompat k.1 l.1)).mono
      ((d k).symm.trans (d l)).open_source hsub).congr heq.symm

end IsLocalHomeomorph

namespace Geometry





theorem PolyhedralPLInCharts.lift
    {V E M X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [TopologicalSpace X]
    {p : X → M} {c : ι → OpenPartialHomeomorph M E}
    (d : ι × X → OpenPartialHomeomorph X E)
    (hcenter : ∀ i x, p x ∈ (c i).source → x ∈ (d (i, x)).source)
    (hval : ∀ k, EqOn (d k) ((c k.1) ∘ p) (d k).source)
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {f : V → M} (hf : PolyhedralPLInCharts c f K.space)
    {g : V → X} (hg : ContinuousOn g K.space) (hpg : EqOn (p ∘ g) f K.space) :
    PolyhedralPLInCharts d g K.space := by
  refine ⟨hg, ?_⟩
  intro x
  obtain ⟨i, J, W, _, _, hW, hxW, hWJ, hfJ, hcoords⟩ := hf.coordinates x
  let k : ι × X := (i, g x)
  let O : Set K.space := W ∩ (fun y : K.space => g y) ⁻¹' (d k).source
  have hgc : Continuous (fun y : K.space => g y) :=
    hg.comp_continuous continuous_subtype_val (fun y => y.property)
  have hO : IsOpen O := hW.inter ((d k).open_source.preimage hgc)
  have hxO : x ∈ O := by
    refine ⟨hxW, hcenter i (g x) ?_⟩
    change (p ∘ g) x ∈ (c i).source
    rw [hpg x.property]
    exact hfJ (hWJ (mem_image_of_mem Subtype.val hxW))
  obtain ⟨L, U, hL, hLK, hU, hxU, hUL, hLO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO hxO
  have hLJ : L.space ⊆ J.space := by
    intro y hy
    have hyO := hLO (show (⟨y, hLK hy⟩ : K.space) ∈ Subtype.val ⁻¹' L.space from hy)
    exact hWJ (mem_image_of_mem Subtype.val hyO.1)
  have hgL : MapsTo g L.space (d k).source := by
    intro y hy
    exact (hLO (show (⟨y, hLK hy⟩ : K.space) ∈ Subtype.val ⁻¹' L.space from hy)).2
  refine ⟨k, L, U, hL, hLK, hU, hxU, hUL, hgL, ?_⟩
  apply (hcoords.restrict L hL hLJ).congr
  intro y hy
  change c i (f y) = d k (g y)
  rw [hval k (hgL hy)]
  exact congrArg (c i) (hpg (hLK hy)).symm

end Geometry
