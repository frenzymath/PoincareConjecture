import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.LocalInverse
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Compact
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Localized










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]


theorem exists_linearization_neighborhood
    (f : E -> E) (hf : ContDiff Real ∞ f)
    (hbij : Function.Bijective (fderiv Real f 0)) :
    ∃ r : Real, 0 < r ∧
      ∃ e : OpenPartialHomeomorph (Real × E) (Real × E),
      Icc (0 : Real) 1 ×ˢ closedBall 0 r ⊆ e.source ∧
      EqOn e (fun z => (z.1, (1 - z.1) • (f z.2 - f 0) + z.1 • fderiv Real f 0 z.2))
        e.source ∧
      ContMDiffOn 𝓘(Real, Real × E) 𝓘(Real, Real × E) ∞ e.symm e.target ∧
      ∀ s ∈ Icc (0 : Real) 1,
      InjOn (fun x => (1 - s) • (f x - f 0) + s • fderiv Real f 0 x)
        (closedBall 0 r) ∧
      ∀ x ∈ closedBall 0 r,
        IsLocalDiffeomorphAt 𝓘(Real, E) 𝓘(Real, E) ∞
          (fun y => (1 - s) • (f y - f 0) + s • fderiv Real f 0 y) x := by
  let A := fderiv Real f 0
  let F : Real × E -> E := fun z => (1 - z.1) • (f z.2 - f 0) + z.1 • A z.2
  have hF : ContDiff Real ∞ F :=
    ((contDiff_const.sub contDiff_fst).smul ((hf.comp contDiff_snd).sub contDiff_const)).add
      (contDiff_fst.smul (A.contDiff.comp contDiff_snd))
  let B : Real × E -> E →L[Real] E := fun z => (1 - z.1) • fderiv Real f z.2 + z.1 • A
  have hB : Continuous B :=
    ((continuous_const.sub continuous_fst).smul
      ((hf.fderiv_right (m := ∞) (by simp)).continuous.comp continuous_snd)).add
      (continuous_fst.smul continuous_const)
  have hB0 (s : Real) : B (s, 0) = A := by
    simp only [B, ← add_smul, sub_add_cancel, one_smul, A]
  have hslice (s : Real) (x : E) :
      fderiv Real (fun y => F (s, y)) x = B (s, x) := by
    exact ((((hf.differentiable (by simp) x).hasFDerivAt.sub_const (f 0)).const_smul
      (1 - s)).add (A.hasFDerivAt.const_smul s)).fderiv
  let H : Real × E -> Real × E := fun z => (z.1, F z)
  have hH : ContDiff Real ∞ H := contDiff_fst.prodMk hF
  let L : (Real × E) →L[Real] (Real × E) :=
    (ContinuousLinearMap.id Real Real).prodMap A
  have hL : Function.Bijective L := by
    exact Function.Bijective.prodMap Function.bijective_id hbij
  have hHder (s : Real) : HasFDerivAt H L (s, 0) := by
    have hdf := (hf.differentiable (by simp) (0 : E)).hasFDerivAt.comp (s, (0 : E))
      (hasFDerivAt_snd (𝕜 := Real) (p := (s, (0 : E))))
    have hda := A.hasFDerivAt.comp (s, (0 : E))
      (hasFDerivAt_snd (𝕜 := Real) (p := (s, (0 : E))))
    have hds := hasFDerivAt_fst (𝕜 := Real) (p := (s, (0 : E)))
    have hd := hds.prodMk
      (((hasFDerivAt_const (1 : Real) (s, (0 : E))).sub hds).smul (hdf.sub_const (f 0)) |>.add
        (hds.smul hda))
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro z
    simp [L, A, ContinuousLinearMap.prodMap, sub_smul]
  let K : Set (Real × E) := Icc (0 : Real) 1 ×ˢ {0}
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hinj : InjOn H K := by
    rintro ⟨s, x⟩ ⟨_, hx⟩ ⟨t, y⟩ ⟨_, hy⟩ heq
    have hst : s = t := congrArg Prod.fst heq
    simp only [mem_singleton_iff] at hx hy
    exact Prod.ext hst (hx.trans hy.symm)
  have hloc : ∀ z ∈ K, IsLocalDiffeomorphAt 𝓘(Real, Real × E)
      𝓘(Real, Real × E) ∞ H z := by
    rintro ⟨s, x⟩ ⟨_, hx⟩
    have hx0 : x = 0 := hx
    subst x
    apply localDiffeomorphAt_of_smooth_bijective_derivative hH
    rw [(hHder s).fderiv]
    exact hL
  obtain ⟨e, he, _, heq, _, hei⟩ :=
    Poincare.exists_openPartialHomeomorph_of_injOn_compact hK hinj hloc
  let U : Set (Real × E) := e.source ∩ {z | IsUnit (B z)}
  have hU : IsOpen U := e.open_source.inter (Units.isOpen.preimage hB)
  have hKU : K ⊆ U := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    have hx0 : x = 0 := hx
    subst x
    refine ⟨he ⟨hs, mem_singleton 0⟩, ?_⟩
    change IsUnit (B (s, 0))
    rw [hB0]
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
  obtain ⟨S, V, _, hV, hS, h0V, hSV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hU hKU
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hV.mem_nhds (h0V (mem_singleton 0)))
  refine ⟨r, hr, e, ?_, heq, hei, fun s hs => ⟨?_, ?_⟩⟩
  · rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact (hSV (show (s, x) ∈ S ×ˢ V from ⟨hS hs, hrV hx⟩)).1
  · intro x hx y hy hxy
    have hxU : (s, x) ∈ U := hSV ⟨hS hs, hrV hx⟩
    have hyU : (s, y) ∈ U := hSV ⟨hS hs, hrV hy⟩
    have hxyH : H (s, x) = H (s, y) := Prod.ext rfl hxy
    have hxyE : e (s, x) = e (s, y) :=
      (heq hxU.1).trans (hxyH.trans (heq hyU.1).symm)
    exact congrArg Prod.snd (e.injOn hxU.1 hyU.1 hxyE)
  · intro x hx
    apply localDiffeomorphAt_of_smooth_bijective_derivative
      (hF.comp (contDiff_const.prodMk contDiff_id))
    change Function.Bijective (fderiv Real (fun y => F (s, y)) x)
    rw [hslice]
    have hxU : (s, x) ∈ U := hSV ⟨hS hs, hrV hx⟩
    exact ContinuousLinearMap.isUnit_iff_bijective.mp hxU.2



theorem exists_uniform_linearization_radius
    (f : E -> E) (hf : ContDiff Real ∞ f)
    (hbij : Function.Bijective (fderiv Real f 0)) :
    ∃ r : Real, 0 < r ∧ ∀ s ∈ Icc (0 : Real) 1,
      InjOn (fun x => (1 - s) • (f x - f 0) + s • fderiv Real f 0 x)
        (closedBall 0 r) ∧
      ∀ x ∈ closedBall 0 r,
        IsLocalDiffeomorphAt 𝓘(Real, E) 𝓘(Real, E) ∞
          (fun y => (1 - s) • (f y - f 0) + s • fderiv Real f 0 y) x := by
  obtain ⟨r, hr, _, _, _, _, h⟩ := exists_linearization_neighborhood f hf hbij
  exact ⟨r, hr, h⟩



theorem exists_supported_linearization_isotopy
    (f : E -> E) (hf : ContDiff Real ∞ f)
    (hbij : Function.Bijective (fderiv Real f 0)) :
    ∃ r : Real, 0 < r ∧
      ∃ Φ : Real -> Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      (∀ x, Φ 0 x = x) ∧
      ContDiff Real ∞ (fun z : Real × E => Φ z.1 z.2) ∧
      (∃ K : Set E, IsCompact K ∧ ∀ s x, x ∉ K -> Φ s x = x) ∧
      ∀ s ∈ Icc (0 : Real) 1, ∀ x ∈ closedBall 0 r,
        Φ s (f x - f 0) = (1 - s) • (f x - f 0) + s • fderiv Real f 0 x := by
  obtain ⟨r, hr, e, hsource, heq, hei, _⟩ := exists_linearization_neighborhood f hf hbij
  let A := fderiv Real f 0
  let F : Real × E -> E := fun z => (1 - z.1) • (f z.2 - f 0) + z.1 • A z.2
  have hF : ContDiff Real ∞ F :=
    ((contDiff_const.sub contDiff_fst).smul ((hf.comp contDiff_snd).sub contDiff_const)).add
      (contDiff_fst.smul (A.contDiff.comp contDiff_snd))
  obtain ⟨Φ, hi, hsmooth, hfix, hmotion⟩ := exists_ambient_isotopy_of_compact_isotopy
    (isCompact_closedBall 0 r) F hF e hsource hei
    (fun s hs x hx => heq (hsource ⟨hs, hx⟩))
  refine ⟨r, hr, Φ, hi, hsmooth, hfix, ?_⟩
  intro s hs x hx
  simpa only [F, A, sub_zero, one_smul, zero_smul, add_zero] using hmotion s hs x hx



theorem exists_supported_linearization_isotopy_within
    (f : E -> E) (hf : ContDiff Real ∞ f)
    (hbij : Function.Bijective (fderiv Real f 0))
    {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U) :
    ∃ r : Real, 0 < r ∧ ∃ S : Set E, IsCompact S ∧ S ⊆ U ∧
      ∃ Phi : Real -> Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      (∀ x, Phi 0 x = x) ∧
      ContDiff Real ∞ (fun z : Real × E => Phi z.1 z.2) ∧
      (∀ s x, x ∉ S -> Phi s x = x) ∧
      ∀ s ∈ Icc (0 : Real) 1, ∀ x ∈ closedBall 0 r,
        Phi s (f x - f 0) = (1 - s) • (f x - f 0) + s • fderiv Real f 0 x := by
  obtain ⟨r0, hr0, e, hsource, heq, hei, _⟩ := exists_linearization_neighborhood f hf hbij
  let A := fderiv Real f 0
  let F : Real × E -> E := fun z => (1 - z.1) • (f z.2 - f 0) + z.1 • A z.2
  have hF : ContDiff Real ∞ F :=
    ((contDiff_const.sub contDiff_fst).smul ((hf.comp contDiff_snd).sub contDiff_const)).add
      (contDiff_fst.smul (A.contDiff.comp contDiff_snd))
  have hzero : Icc (0 : Real) 1 ×ˢ ({0} : Set E) ⊆ F ⁻¹' U := by
    rintro ⟨s, x⟩ ⟨_, hx⟩
    have hx0 : x = 0 := hx
    simpa [F, hx0] using h0U
  obtain ⟨J, V, _, hV, hIJ, h0V, hJV⟩ := generalized_tube_lemma
    isCompact_Icc isCompact_singleton (hU.preimage hF.continuous) hzero
  obtain ⟨delta, hdelta, hdeltaV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hV.mem_nhds (h0V (mem_singleton 0)))
  let r := min r0 delta
  have hr : 0 < r := lt_min hr0 hdelta
  have hrsub : closedBall (0 : E) r ⊆ closedBall 0 r0 :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hrV : closedBall (0 : E) r ⊆ V :=
    (closedBall_subset_closedBall (min_le_right _ _)).trans hdeltaV
  have hsource' : Icc (0 : Real) 1 ×ˢ closedBall (0 : E) r ⊆ e.source :=
    (prod_mono subset_rfl hrsub).trans hsource
  obtain ⟨S, hS, hSU, Phi, hi, hs, hfix, hmotion⟩ :=
    exists_ambient_isotopy_of_compact_isotopy_within (isCompact_closedBall 0 r) hU
      F hF e hsource' hei (fun s hs x hx => heq (hsource' ⟨hs, hx⟩))
      (fun s hs x hx => hJV ⟨hIJ hs, hrV hx⟩)
  refine ⟨r, hr, S, hS, hSU, Phi, hi, hs, hfix, ?_⟩
  intro s hs x hx
  simpa only [F, A, sub_zero, one_smul, zero_smul, add_zero] using hmotion s hs x hx

end Poincare.Manifold.Schoenflies
