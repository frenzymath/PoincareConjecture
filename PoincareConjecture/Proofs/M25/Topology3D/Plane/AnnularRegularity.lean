import PoincareConjecture.Proofs.M25.Topology3D.Plane.AnnularExtension










set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D




theorem exists_smoothTrack_localInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : ℝ × E → E) (p : ℝ × E) (hA : ContDiffAt ℝ ∞ A p)
    (hi : Injective (fderiv ℝ (fun x => A (p.1, x)) p.2)) :
    ∃ e : OpenPartialHomeomorph (ℝ × E) (ℝ × E), p ∈ e.source ∧
      (∀ y : ℝ × E, e y = (y.1, A y)) ∧ ContDiffAt ℝ ∞ e.symm (p.1, A p) := by
  let T : ℝ × E → ℝ × E := fun y => (y.1, A y)
  let L := fderiv ℝ A p
  let D := fderiv ℝ (fun x => A (p.1, x)) p.2
  have hbij : Bijective D.toLinearMap := ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  let d : E ≃L[ℝ] E := (LinearEquiv.ofBijective D.toLinearMap hbij).toContinuousLinearEquiv
  have hAD : HasFDerivAt A L p := (hA.differentiableAt (by simp)).hasFDerivAt
  have hsp : L.comp (ContinuousLinearMap.inr ℝ ℝ E) = (d : E →L[ℝ] E) := by
    have hAD' : HasFDerivAt A L (p.1, p.2) := hAD
    have hinner : HasFDerivAt (fun x : E => (p.1, x))
        (ContinuousLinearMap.inr ℝ ℝ E) p.2 := hasFDerivAt_prodMk_right p.1 p.2
    have h := hAD'.comp p.2 hinner
    exact h.fderiv.symm
  let B : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).skewProd d (L.comp (ContinuousLinearMap.inl ℝ ℝ E))
  have hB : (B : ℝ × E →L[ℝ] ℝ × E) = (ContinuousLinearMap.fst ℝ ℝ E).prod L := by
    apply ContinuousLinearMap.ext
    intro y
    apply Prod.ext
    · rfl
    · change d y.2 + L (y.1, 0) = L y
      have hd : d y.2 = L (0, y.2) :=
        (congrArg (fun f : E →L[ℝ] E => f y.2) hsp).symm
      rw [hd, ← map_add]
      simp
  have hTD : HasFDerivAt T (B : ℝ × E →L[ℝ] ℝ × E) p := by
    rw [hB]
    exact hasFDerivAt_fst.prodMk hAD
  have hT : ContDiffAt ℝ ∞ T p := contDiffAt_fst.prodMk hA
  let e := hT.toOpenPartialHomeomorph T hTD (by simp)
  exact ⟨e, hT.mem_toOpenPartialHomeomorph_source hTD (by simp), fun _ => rfl,
    hT.to_localInverse hTD (by simp)⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
variable (c : ℝ → sphere (0 : E) 1 → E)
variable (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
  (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))

include hc



theorem contDiffAt_curveAnnularExtension_of_regular {p : ℝ × E} (hx : p.2 ≠ 0)
    (hv : curveFamilyVelocity o (radialFamilyExtension q0 c)
      (p.1, (unitRadialProjection q0 p.2 : E)) ≠ 0) :
    ContDiffAt ℝ ∞ (curveAnnularExtension o q0 c) p := by
  have hC : ContDiffAt ℝ ∞ (radialFamilyExtension q0 c) p :=
    (contDiffOn_radialFamilyExtension q0 c hc).contDiffAt
    ((isOpen_univ.prod isClosed_singleton.isOpen_compl).mem_nhds ⟨mem_univ _, hx⟩)
  have hP : ContDiffAt ℝ ∞ (fun x : E => (unitRadialProjection q0 x : E)) p.2 :=
    contDiffAt_unitRadialProjection_coe q0 hx
  have hR : ContDiffAt ℝ ∞
      (fun y : ℝ × E => (y.1, (unitRadialProjection q0 y.2 : E))) p :=
    contDiffAt_fst.prodMk (hP.comp p contDiffAt_snd)
  have hCR : ContDiffAt ℝ ∞ (radialFamilyExtension q0 c)
      (p.1, (unitRadialProjection q0 p.2 : E)) :=
    (contDiffOn_radialFamilyExtension q0 c hc).contDiffAt
    ((isOpen_univ.prod isClosed_singleton.isOpen_compl).mem_nhds
      ⟨mem_univ _, ne_zero_of_mem_unit_sphere (unitRadialProjection q0 p.2)⟩)
  have hN := contDiffAt_curveFamilyNormal o hCR hv
  have hNR : ContDiffAt ℝ ∞ (fun y : ℝ × E =>
      curveFamilyNormal o (radialFamilyExtension q0 c)
        (y.1, (unitRadialProjection q0 y.2 : E))) p :=
    ContDiffAt.comp (g := curveFamilyNormal o (radialFamilyExtension q0 c))
      (f := fun y : ℝ × E => (y.1, (unitRadialProjection q0 y.2 : E))) p hN hR
  exact hC.add ((((contDiffAt_norm ℝ hx).comp p contDiffAt_snd).sub
    contDiffAt_const).smul hNR)




theorem exists_open_curveAnnularRegularNeighborhood :
    ∃ U : Set (ℝ × E), IsOpen U ∧
      (∀ z : ℝ, ∀ q : sphere (0 : E) 1,
        curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E)) ≠ 0 →
          (z, (q : E)) ∈ U) ∧
      (∀ p ∈ U, p.2 ≠ 0 ∧ ContDiffAt ℝ ∞ (curveAnnularExtension o q0 c) p ∧
        Injective (fderiv ℝ (fun x => curveAnnularExtension o q0 c (p.1, x)) p.2)) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 from Fact.out]
    norm_num)
  let H : Set (ℝ × E) := univ ×ˢ ({0} : Set E)ᶜ
  let W : ℝ × E → E := fun p => curveFamilyVelocity o (radialFamilyExtension q0 c)
    (p.1, (unitRadialProjection q0 p.2 : E))
  have hH : IsOpen H := isOpen_univ.prod isClosed_singleton.isOpen_compl
  have hW : ContinuousOn W H := by
    intro p hp
    have hP : ContDiffAt ℝ ∞ (fun x : E => (unitRadialProjection q0 x : E)) p.2 :=
      contDiffAt_unitRadialProjection_coe q0 hp.2
    have hR : ContDiffAt ℝ ∞
        (fun y : ℝ × E => (y.1, (unitRadialProjection q0 y.2 : E))) p :=
      contDiffAt_fst.prodMk (hP.comp p contDiffAt_snd)
    have hCR : ContDiffAt ℝ ∞ (radialFamilyExtension q0 c)
        (p.1, (unitRadialProjection q0 p.2 : E)) :=
      (contDiffOn_radialFamilyExtension q0 c hc).contDiffAt
      (hH.mem_nhds ⟨mem_univ _, ne_zero_of_mem_unit_sphere (unitRadialProjection q0 p.2)⟩)
    have hV := contDiffAt_curveFamilyVelocity o hCR
    have hWR : ContDiffAt ℝ ∞ W p :=
      ContDiffAt.comp (g := curveFamilyVelocity o (radialFamilyExtension q0 c))
        (f := fun y : ℝ × E => (y.1, (unitRadialProjection q0 y.2 : E))) p hV hR
    exact hWR.continuousAt.continuousWithinAt
  let B := H ∩ W ⁻¹' ({0} : Set E)ᶜ
  have hB : IsOpen B := hW.isOpen_inter_preimage hH isClosed_singleton.isOpen_compl
  let A := curveAnnularExtension o q0 c
  have hA : ∀ p ∈ B, ContDiffAt ℝ ∞ A p := fun p hp =>
    contDiffAt_curveAnnularExtension_of_regular o q0 c hc hp.1.2 hp.2
  let D : ℝ × E → E →L[ℝ] E := fun p => fderiv ℝ (fun x => A (p.1, x)) p.2
  have hD : ContinuousOn D B := by
    intro p hp
    have hcomp : ContDiffAt ℝ ∞ (fun y : (ℝ × E) × E => A (y.1.1, y.2)) (p, p.2) :=
      (hA p hp).comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞ D p :=
      ContDiffAt.fderiv (f := fun y : ℝ × E => fun x : E => A (y.1, x))
        (g := (Prod.snd : ℝ × E → E)) hcomp contDiffAt_snd (by simp)
    exact hd.continuousAt.continuousWithinAt
  let U := B ∩ D ⁻¹' {L : E →L[ℝ] E | Injective L}
  refine ⟨U, hD.isOpen_inter_preimage hB ContinuousLinearMap.isOpen_injective, ?_, ?_⟩
  · intro z q hv
    refine ⟨⟨⟨mem_univ _, ne_zero_of_mem_unit_sphere q⟩, ?_⟩,
      (bijective_fderiv_curveAnnularExtension o q0 c hc z q hv).1⟩
    simpa only [W, mem_preimage, mem_compl_iff, mem_singleton_iff,
      unitRadialProjection_apply_coe] using hv
  · intro p hp
    exact ⟨hp.1.1.2, hA p hp.1, hp.2⟩

end PoincareConjecture.M25.Topology3D
