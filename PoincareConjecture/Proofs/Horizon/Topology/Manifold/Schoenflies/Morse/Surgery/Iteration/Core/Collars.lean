import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Belt
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.Tube



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩
private instance : ChartedSpace (E1 × Real) (S1 × Real) := prodChartedSpace E1 S1 Real Real
private instance : Nonempty S2 := by
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : E3))).mpr zero_le_one
  exact ⟨⟨x, hx⟩⟩

private theorem exists_annular_chart_lifting_cylinder
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {v : E3} {c ε : Real}
    (H : S1 × Real → E3) (hH : ContMDiff Iprod (𝓡 3) ∞ H)
    (himage : ∀ z ∈ univ ×ˢ Ioo (-ε) ε, H z ∈ range g)
    (hheight : ∀ z, inner Real v (H z) = c + z.2)
    (Q : E3 → E2) (hQ : ContMDiff (𝓡 3) (𝓡 2) ∞ Q)
    (hQH : ∀ z, Q (H z) = (z.1 : E2)) :
    ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (-ε) ε ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      ∀ z ∈ F.source, g (F z) = H z := by
  let U : Set (S1 × Real) := univ ×ˢ Ioo (-ε) ε
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  let K : S1 × Real → S2 := invFun g ∘ H
  have hKg : ∀ z ∈ U, g (K z) = H z := fun z hz => invFun_eq (himage z hz)
  have hK : ContMDiffOn Iprod (𝓡 2) ∞ K U := by
    intro z hz
    have heq : g ∘ K =ᶠ[𝓝 z] H := eventuallyEq_of_mem (hU.mem_nhds hz) hKg
    have hcomp : ContMDiffAt Iprod (𝓡 3) ∞ (g ∘ K) z :=
      (hH z).congr_of_eventuallyEq heq
    exact ((ContMDiffAt.iff_comp_isImmersionAt (hg.isImmersion.isImmersionAt (K z))).mpr
      ⟨hg.isEmbedding.isInducing.continuousAt_iff.mpr hcomp.continuousAt, hcomp⟩).contMDiffWithinAt
  have hKh : ∀ z ∈ U, inner Real v (g (K z)) = c + z.2 := by
    intro z hz
    rw [hKg z hz, hheight]
  have hKinj : InjOn K U := by
    intro z hz w hw hzw
    have hHw : H z = H w := (hKg z hz).symm.trans ((congrArg g hzw).trans (hKg w hw))
    apply Prod.ext
    · apply Subtype.ext
      exact (hQH z).symm.trans ((congrArg Q hHw).trans (hQH w))
    · exact add_left_cancel ((hheight z).symm.trans
        ((congrArg (inner Real v) hHw).trans (hheight w)))
  have hslice : ∀ z ∈ U,
      Injective (mfderiv (𝓡 1) (𝓡 2) (fun q => K (q, z.2)) z.1) := by
    intro z hz
    have hpair : ContMDiffAt (𝓡 1) Iprod ∞ (fun q : S1 => (q, z.2)) z.1 :=
      contMDiffAt_id.prodMk contMDiffAt_const
    have hKs : ContMDiffAt (𝓡 1) (𝓡 2) ∞ (fun q => K (q, z.2)) z.1 :=
      (hK.contMDiffAt (hU.mem_nhds hz)).comp
        (g := K) (f := fun q : S1 => (q, z.2)) z.1 hpair
    have heq : (Q ∘ g) ∘ (fun q => K (q, z.2)) = (Subtype.val : S1 → E2) := by
      funext q
      change Q (g (K (q, z.2))) = _
      rw [hKg (q, z.2) ⟨mem_univ _, hz.2⟩, hQH]
    have hchain := mfderiv_comp z.1
      ((hQ.comp hg.contMDiff).mdifferentiable (by simp) _) (hKs.mdifferentiableAt (by simp))
    rw [heq] at hchain
    have hinj : Injective (mfderiv (𝓡 1) (𝓡 2) (Subtype.val : S1 → E2) z.1) := by
      convert! injective_mvfderiv_subtypeVal_sphere z.1
    rw [hchain] at hinj
    intro u w huw
    apply hinj
    exact congrArg (mfderiv (𝓡 2) (𝓡 2) (Q ∘ g) (K z)) huw
  have hbij := bijective_mfderiv_of_height_and_slices
    ((innerSL Real v).contMDiff.comp hg.contMDiff) hU hK c hKh hslice
  obtain ⟨F, hFs, hFK, hF, hFi⟩ :=
    exists_annular_chart_of_injective_bijective_derivative hU hK hKinj hbij
  exact ⟨F, hFs, hF, hFi, fun z hz => by rw [hFK]; exact hKg z (hFs ▸ hz)⟩

private theorem normalized_belt_height {s t δ : Real} (hs : s ≠ 0)
    (hδ : δ ≤ |s| / 2) (ht : t ∈ Ioo (-δ) δ) :
    (1 / 2 : Real) + t / s ∈ Ioo 0 1 := by
  have hb : |t / s| < (1 / 2 : Real) := by
    rw [abs_div, div_lt_iff₀ (abs_pos.mpr hs)]
    have h := abs_lt.mpr ht
    nlinarith
  obtain ⟨hl, hu⟩ := abs_lt.mp hb
  constructor <;> linarith

namespace SphereSurgeryCoreCap

variable {v : E3} {g : S2 → E3} {B : Set Real}




theorem exists_cylindrical_belt_chart_of_width (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {δ : Real} (hδ : δ ≤ |D.scale| / 2) :
    ∃ (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
      (F : OpenPartialHomeomorph (S1 × Real) S2),
      F.source = univ ×ˢ Ioo (-δ) δ ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (-δ) δ →
        g (F (q, t)) = (D.center + D.scale / 2 + t) • v +
          (D.planeMap (J.symm (q : E2)) : E3)) ∧
      F.target = (D.chart '' closedBall 0 1) ∩
        {p : S2 | |inner Real v (g p) - (D.center + D.scale / 2)| < δ} ∧
      F.target ⊆ D.chart '' ball 0 1 := by
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by
      intro heq
      simpa [heq] using D.unit_v)).repr
  let H : S1 × Real → E3 := fun z => heightCoordinates D.unit_v
    (D.center + D.scale / 2 + z.2, D.planeMap (J.symm (z.1 : E2)))
  let Q : E3 → E2 := fun y => J (D.planeMap.symm
    ((Hemisphere.Plane v).orthogonalProjectionOnto y))
  have hγ : ContMDiff (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞
      (fun q : S1 => D.planeMap (J.symm (q : E2))) :=
    D.planeMap.contMDiff.comp (J.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp
      contMDiff_coe_sphere)
  have hH : ContMDiff Iprod (𝓡 3) ∞ H := by
    change ContMDiff Iprod (𝓡 3) ∞ (fun z : S1 × Real =>
      (D.center + D.scale / 2 + z.2) • v + (D.planeMap (J.symm (z.1 : E2)) : E3))
    exact ((contMDiff_const.add contMDiff_snd).smul contMDiff_const).add
      ((Hemisphere.Plane v).subtypeL.contMDiff.comp (hγ.comp contMDiff_fst))
  have hQ : ContMDiff (𝓡 3) (𝓡 2) ∞ Q :=
    J.toContinuousLinearEquiv.contDiff.contMDiff.comp
      (D.planeMap.symm.contMDiff.comp (Hemisphere.Plane v).orthogonalProjectionOnto.contMDiff)
  have hheight : ∀ z, inner Real v (H z) = D.center + D.scale / 2 + z.2 :=
    fun z => inner_heightCoordinates D.unit_v _
  have hQH : ∀ z, Q (H z) = (z.1 : E2) := by
    intro z
    have hp : (Hemisphere.Plane v).orthogonalProjectionOnto (H z) =
        D.planeMap (J.symm (z.1 : E2)) :=
      congrArg Prod.snd ((heightCoordinates D.unit_v).symm_apply_apply _)
    change J (D.planeMap.symm ((Hemisphere.Plane v).orthogonalProjectionOnto (H z))) = _
    rw [hp, D.planeMap.symm_apply_apply, J.apply_symm_apply]
  have hclock (t : Real) : D.center + D.scale * (1 / 2 + t / D.scale) =
      D.center + D.scale / 2 + t := by field_simp [D.scale_ne_zero]; ring
  have hcap : ∀ z ∈ univ ×ˢ Ioo (-δ) δ,
      H z ∈ D.parametrization '' closedBall 0 1 := by
    intro z hz
    have ht := normalized_belt_height D.scale_ne_zero hδ hz.2
    have hm : H z ∈ (fun x : Hemisphere.Plane v =>
        (D.center + D.scale * (1 / 2 + z.2 / D.scale)) • v + (D.planeMap x : E3)) ''
          sphere (0 : Hemisphere.Plane v) 1 := by
      refine ⟨J.symm (z.1 : E2), ?_, ?_⟩
      · simp only [mem_sphere_zero_iff_norm, J.symm.norm_map, norm_eq_of_mem_sphere]
      · rw [hclock]
        rfl
    rw [← lifted_cap_slice_eq_circle D.unit_v D.center D.scale D.scale_ne_zero
      D.planeMap ⟨ht.1.le, ht.2⟩] at hm
    rw [D.range_eq]
    exact hm.1
  have himage : ∀ z ∈ univ ×ˢ Ioo (-δ) δ, H z ∈ range g := by
    intro z hz
    obtain ⟨x, hx, hxy⟩ := hcap z hz
    exact ⟨D.chart x, (D.parametrization_eq x hx).trans hxy⟩
  obtain ⟨F, hFs, hF, hFi, hFg⟩ := exists_annular_chart_lifting_cylinder hg
    H hH himage hheight Q hQ hQH
  have htarget : F.target = (D.chart '' closedBall 0 1) ∩
      {p : S2 | |inner Real v (g p) - (D.center + D.scale / 2)| < δ} := by
    rw [← F.image_source_eq_target]
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hcap z (hFs ▸ hz)
      refine ⟨⟨x, hx, hg.isEmbedding.injective ?_⟩, ?_⟩
      · exact (D.parametrization_eq x hx).trans (hxy.trans (hFg z hz).symm)
      · change |inner Real v (g (F z)) - (D.center + D.scale / 2)| < δ
        rw [hFg z hz, hheight, add_sub_cancel_left]
        exact abs_lt.mpr (hFs ▸ hz).2
    · rintro ⟨hpD, hpheight⟩
      let t := inner Real v (g p) - (D.center + D.scale / 2)
      have ht : t ∈ Ioo (-δ) δ := abs_lt.mp hpheight
      have htnorm := normalized_belt_height D.scale_ne_zero hδ ht
      have hgpcap : g p ∈ D.parametrization '' closedBall 0 1 :=
        D.image_closedBall ▸ mem_image_of_mem g hpD
      rw [D.range_eq] at hgpcap
      have hgpheight : inner Real v (g p) = D.center + D.scale * (1 / 2 + t / D.scale) := by
        rw [hclock]
        dsimp [t]
        ring
      have hslice : g p ∈ (fun x : Hemisphere.Plane v =>
          (D.center + D.scale * (1 / 2 + t / D.scale)) • v + (D.planeMap x : E3)) ''
            sphere (0 : Hemisphere.Plane v) 1 := by
        rw [← lifted_cap_slice_eq_circle D.unit_v D.center D.scale D.scale_ne_zero
          D.planeMap ⟨htnorm.1.le, htnorm.2⟩]
        exact ⟨hgpcap, hgpheight⟩
      obtain ⟨x, hx, hxp⟩ := hslice
      let q : S1 := ⟨J x, by simpa only [mem_sphere_zero_iff_norm, J.norm_map] using hx⟩
      have hz : (q, t) ∈ F.source := by rw [hFs]; exact ⟨mem_univ _, ht⟩
      refine ⟨(q, t), hz, hg.isEmbedding.injective ?_⟩
      rw [hFg (q, t) hz]
      change (D.center + D.scale / 2 + t) • v +
        (D.planeMap (J.symm (J x)) : E3) = g p
      rw [J.symm_apply_apply]
      simpa only [hclock] using hxp
  refine ⟨J, F, hFs, hF, hFi, ?_, htarget, ?_⟩
  · intro q t ht
    exact hFg (q, t) (by rw [hFs]; exact ⟨mem_univ _, ht⟩)
  · intro p hp
    rw [htarget] at hp
    obtain ⟨x, hx, rfl⟩ := hp.1
    refine ⟨x, ?_, rfl⟩
    rw [mem_ball_zero_iff]
    have hxle := mem_closedBall_zero_iff.mp hx
    by_contra hxnot
    have hxsphere : x ∈ sphere (0 : E2) 1 :=
      mem_sphere_zero_iff_norm.mpr (le_antisymm hxle (le_of_not_gt hxnot))
    have heq : inner Real v (g (D.chart x)) = D.center :=
      (congrArg (inner Real v) (D.parametrization_eq x hx)).trans (D.boundary_height x hxsphere)
    have hh := hp.2
    change |inner Real v (g (D.chart x)) - (D.center + D.scale / 2)| < δ at hh
    rw [heq, show D.center - (D.center + D.scale / 2) = -D.scale / 2 by ring,
      abs_div, abs_neg, abs_of_pos (by norm_num : (0 : Real) < 2)] at hh
    linarith [abs_pos.mpr D.scale_ne_zero]


theorem exists_cylindrical_belt_chart (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) :
    ∃ (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
      (F : OpenPartialHomeomorph (S1 × Real) S2),
      F.source = univ ×ˢ Ioo (-(|D.scale| / 4)) (|D.scale| / 4) ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (-(|D.scale| / 4)) (|D.scale| / 4) →
        g (F (q, t)) = (D.center + D.scale / 2 + t) • v +
          (D.planeMap (J.symm (q : E2)) : E3)) ∧
      F.target = (D.chart '' closedBall 0 1) ∩
        {p : S2 | |inner Real v (g p) - (D.center + D.scale / 2)| < |D.scale| / 4} ∧
      F.target ⊆ D.chart '' ball 0 1 :=
  D.exists_cylindrical_belt_chart_of_width hg (by linarith [abs_nonneg D.scale])



theorem regular_on_open_cylindrical_belt (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {p : S2} (hp : p ∈ D.chart '' closedBall 0 1)
    (hhp : |inner Real v (g p) - (D.center + D.scale / 2)| < |D.scale| / 2) :
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0 := by
  obtain ⟨J, F, hFs, hF, _, hFg, htarget, _⟩ :=
    D.exists_cylindrical_belt_chart_of_width hg le_rfl
  have hpF : p ∈ F.target := htarget ▸ ⟨hp, hhp⟩
  let z := F.symm p
  have hz : z ∈ F.source := F.map_target hpF
  have hFp : F z = p := F.right_inv hpF
  let h : S2 → Real := fun q => inner Real v (g q)
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real v).contMDiff.comp hg.contMDiff
  have heq : h ∘ F =ᶠ[𝓝 z] (fun w : S1 × Real => D.center + D.scale / 2 + w.2) := by
    filter_upwards [F.open_source.mem_nhds hz] with w hw
    change inner Real v (g (F w)) = _
    rw [hFg w.1 w.2 (hFs ▸ hw).2]
    simp [inner_add_right, inner_smul_right, D.unit_v,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (D.planeMap _).property]
  have hderiv : mfderiv Iprod 𝓘(Real, Real)
      (fun w : S1 × Real => D.center + D.scale / 2 + w.2) z =
        ContinuousLinearMap.snd Real E1 Real := by
    change mfderiv Iprod 𝓘(Real, Real)
      ((fun _ : S1 × Real => D.center + D.scale / 2) + Prod.snd) z = _
    rw [mfderiv_add mdifferentiableAt_const mdifferentiableAt_snd,
      mfderiv_const, zero_add, mfderiv_snd]
    rfl
  have hchain := mfderiv_comp z (hh.mdifferentiable (by simp) (F z))
    ((hF.contMDiffAt (F.open_source.mem_nhds hz)).mdifferentiableAt (by simp))
  rw [heq.mfderiv_eq, hderiv, hFp] at hchain
  intro hzero
  change mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0 at hzero
  rw [hzero, ContinuousLinearMap.zero_comp] at hchain
  have hbad := congrArg (fun L : E1 × Real →L[Real] Real => L (0, 1)) hchain
  norm_num at hbad


theorem regular_on_cylindrical_belt (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {p : S2} (hp : p ∈ D.chart '' closedBall 0 1)
    (hhp : |inner Real v (g p) - (D.center + D.scale / 2)| < |D.scale| / 4) :
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0 :=
  D.regular_on_open_cylindrical_belt hg hp (by linarith [abs_pos.mpr D.scale_ne_zero])

end SphereSurgeryCoreCap

end Poincare.Manifold.Schoenflies
