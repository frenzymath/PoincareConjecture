import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfilePath
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapEmbedding
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartTimeField
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable (a0 a1 : ℝ → ℝ) (b0 b1 : E2 → ℝ)
variable (ha0 : ContDiff ℝ ∞ a0) (ha1 : ContDiff ℝ ∞ a1)
variable (hb0 : ContDiff ℝ ∞ b0) (hb1 : ContDiff ℝ ∞ b1)
variable (hapos0 : ∀ v, 0 < a0 v) (hapos1 : ∀ v, 0 < a1 v)
variable (hbpos0 : ∀ x, 0 < b0 x) (hbpos1 : ∀ x, 0 < b1 x)
variable (T : OpenPartialHomeomorph (E2 × ℝ) E3)
variable (m sigma c lambda : ℝ) (hsigma : sigma ≠ 0) (hlambda : lambda ≠ 0)

local notation "M" => stackCapProfilePath a0 a1 b0 b1
local notation "D" => stackCapProfilePathDiffeomorph a0 a1 b0 b1
  ha0 ha1 hb0 hb1 hapos0 hapos1 hbpos0 hbpos1
local notation "P" => surgeryCapPlacementDiffeomorph m sigma c lambda hsigma hlambda

noncomputable def stackPlacedProfileChart :
    OpenPartialHomeomorph (ℝ × E3) (ℝ × E3) :=
  let chart := (((Homeomorph.refl ℝ).prodCongr heightCoordinates.toHomeomorph).trans
    (D).toHomeomorph).trans ((Homeomorph.refl ℝ).prodCongr (P).toHomeomorph)
  chart.toOpenPartialHomeomorph.trans ((OpenPartialHomeomorph.refl ℝ).prod T)

local notation "e" => stackPlacedProfileChart a0 a1 b0 b1
  ha0 ha1 hb0 hb1 hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda hsigma hlambda

@[simp] theorem stackPlacedProfileChart_apply (t : ℝ) (x : E3) :
    e (t, x) = (t, T (P (M t (heightCoordinates x)))) := rfl

theorem stackPlacedProfileChart_source :
    (e).source = {p : ℝ × E3 | P (M p.1 (heightCoordinates p.2)) ∈ T.source} := by
  ext p
  change (True ∧ (True ∧ P (M p.1 (heightCoordinates p.2)) ∈ T.source)) ↔ _
  simp only [true_and, mem_ofPred_eq]

theorem stackPlacedProfileChart_target : (e).target = univ ×ˢ T.target := by
  ext p
  change ((True ∧ p.2 ∈ T.target) ∧ True) ↔ (True ∧ p.2 ∈ T.target)
  simp only [and_true]

@[simp] theorem stackPlacedProfileChart_symm_apply (t : ℝ) (y : E3) :
    (e).symm (t, y) =
      (t, heightCoordinates.symm (((D).symm (t, (P).symm (T.symm y))).2)) := rfl

theorem stackPlacedProfileChart_contDiffOn
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target) :
    ContDiffOn ℝ ∞ e (e).source ∧ ContDiffOn ℝ ∞ (e).symm (e).target := by
  have hM : ContDiff ℝ ∞ (fun p : ℝ × E3 => M p.1 (heightCoordinates p.2)) :=
    (((D).contMDiff_toFun.contDiff).comp
      (contDiff_fst.prodMk (heightCoordinates.contDiff.comp contDiff_snd))).snd
  have hP : ContDiff ℝ ∞ (fun p : ℝ × E3 => P (M p.1 (heightCoordinates p.2))) :=
    (P).contMDiff_toFun.contDiff.comp hM
  have hforward : ContDiffOn ℝ ∞
      (fun p : ℝ × E3 => T (P (M p.1 (heightCoordinates p.2)))) (e).source :=
    hT.comp hP.contDiffOn (fun p hp => by
      simpa only [stackPlacedProfileChart_source, mem_ofPred_eq] using hp)
  have hTubeInv : ContDiffOn ℝ ∞ (fun p : ℝ × E3 => T.symm p.2) (e).target :=
    hTi.comp contDiff_snd.contDiffOn (fun p hp => by
      rw [stackPlacedProfileChart_target] at hp
      exact hp.2)
  have hPlaceInv : ContDiffOn ℝ ∞
      (fun p : ℝ × E3 => (P).symm (T.symm p.2)) (e).target :=
    (P).symm.contMDiff_toFun.contDiff.comp_contDiffOn hTubeInv
  have hProfileInv : ContDiffOn ℝ ∞
      (fun p : ℝ × E3 => (D).symm (p.1, (P).symm (T.symm p.2))) (e).target :=
    (D).symm.contMDiff_toFun.contDiff.comp_contDiffOn
      (contDiff_fst.contDiffOn.prodMk hPlaceInv)
  exact ⟨contDiff_fst.contDiffOn.prodMk hforward,
    contDiff_fst.contDiffOn.prodMk
      (heightCoordinates.symm.contDiff.comp_contDiffOn hProfileInv.snd)⟩

theorem stackPlacedProfileChart_time (p : ℝ × E3) : (e p).1 = p.1 := rfl

noncomputable def stackPlacedProfileCap (t : ℝ) (q : UnitTwoSphere) : E3 :=
  let p := M t (heightCoordinates (q : E3))
  T (p.1, m + sigma * (c + lambda * p.2))

local notation "cap" => stackPlacedProfileCap a0 a1 b0 b1 T m sigma c lambda

include ha0 ha1 hb0 hb1 hapos0 hapos1 hbpos0 hbpos1 in

theorem stackPlacedProfileCoordinates_mem_source
    (habound0 : ∀ v, |v| < 1 → a0 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (habound1 : ∀ v, |v| < 1 → a1 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (t : ℝ) (q : UnitTwoSphere) :
    ((M t (heightCoordinates (q : E3))).1,
      m + sigma * (c + lambda * (M t (heightCoordinates (q : E3))).2)) ∈ T.source := by
  apply hsource
  exact ⟨mem_closedBall_zero_iff.mpr
    (stackCapProfilePath_fst_norm_le a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 habound0 habound1 t
      (heightCoordinates (q : E3)) (sphere_height_coordinates_sq q).le), mem_univ _⟩

include ha0 ha1 hb0 hb1 hapos0 hapos1 hbpos0 hbpos1 in

theorem stackPlacedProfileCap_contMDiff
    (habound0 : ∀ v, |v| < 1 → a0 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (habound1 : ∀ v, |v| < 1 → a1 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) ∞
      (fun p : ℝ × UnitTwoSphere => cap p.1 p.2) := by
  have hA : ContDiff ℝ ∞ (fun p : E2 × ℝ =>
      (p.1, m + sigma * (c + lambda * p.2))) :=
    contDiff_fst.prodMk (contDiff_const.add
      (contDiff_const.mul (contDiff_const.add (contDiff_const.mul contDiff_snd))))
  have hp := hA.comp_contMDiff
    (stackCapProfilePath_native_contMDiff a0 a1 b0 b1 ha0 ha1 hb0 hb1)
  apply contMDiffOn_univ.mp
  exact hT.contMDiffOn.comp hp.contMDiffOn (fun p _ =>
    stackPlacedProfileCoordinates_mem_source a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda
      habound0 habound1 hsource p.1 p.2)

theorem stackPlacedProfileCap_hasDerivAt
    (habound0 : ∀ v, |v| < 1 → a0 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (habound1 : ∀ v, |v| < 1 → a1 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target) (t : ℝ) (q : UnitTwoSphere) :
    HasDerivAt (fun z => cap z q) (chartTimeField e (t, cap t q)) t := by
  have hp : (t, (q : E3)) ∈ (e).source := by
    rw [stackPlacedProfileChart_source]
    exact stackPlacedProfileCoordinates_mem_source a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda
      habound0 habound1 hsource t q
  exact chartTimeField_track e
    (stackPlacedProfileChart_contDiffOn a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda hsigma hlambda hT hTi).1
    (fun p _ => stackPlacedProfileChart_time a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda hsigma hlambda p)
    t (q : E3) hp

theorem stackPlacedProfileCap_endpoints (q : UnitTwoSphere) :
    cap 0 q = surgeryCapMap a0 b0 ha0 hb0 (fun v => (hapos0 v).ne')
      (fun x => (hbpos0 x).ne') T m sigma c lambda q ∧
    cap 1 q = surgeryCapMap a1 b1 ha1 hb1 (fun v => (hapos1 v).ne')
      (fun x => (hbpos1 x).ne') T m sigma c lambda q := by
  constructor
  · simp only [stackPlacedProfileCap, stackCapProfilePath,
      stackProfileBlend_of_nonpos a0 a1 0 le_rfl,
      stackProfileBlend_of_nonpos b0 b1 0 le_rfl, surgeryCapMap,
      surgeryCapCoordinates, surgeryCapModel, flatCapDiffeomorph_apply]
  · simp only [stackPlacedProfileCap, stackCapProfilePath,
      stackProfileBlend_of_one_le a0 a1 1 le_rfl,
      stackProfileBlend_of_one_le b0 b1 1 le_rfl, surgeryCapMap,
      surgeryCapCoordinates, surgeryCapModel, flatCapDiffeomorph_apply]

theorem stackPlacedProfileCap_isCompact_track
    (habound0 : ∀ v, |v| < 1 → a0 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (habound1 : ∀ v, |v| < 1 → a1 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source) :
    IsCompact ((fun p : ℝ × UnitTwoSphere => (p.1, cap p.1 p.2)) ''
      (Icc (-1 : ℝ) 2 ×ˢ {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0})) ∧
    (fun p : ℝ × UnitTwoSphere => (p.1, cap p.1 p.2)) ''
      (Icc (-1 : ℝ) 2 ×ˢ {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0})
        ⊆ (e).target := by
  have hheight : Continuous (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2) :=
    (heightCoordinates.continuous.comp continuous_subtype_val).snd
  have hQ : IsCompact {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} :=
    (isClosed_le hheight continuous_const).isCompact
  have hcap := (stackPlacedProfileCap_contMDiff a0 a1 b0 b1 ha0 ha1 hb0 hb1
    hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda
    habound0 habound1 hsource hT).continuous
  refine ⟨(isCompact_Icc.prod hQ).image (continuous_fst.prodMk hcap), ?_⟩
  rintro p ⟨⟨t, q⟩, _, rfl⟩
  rw [stackPlacedProfileChart_target]
  exact ⟨mem_univ _, T.map_source
    (stackPlacedProfileCoordinates_mem_source a0 a1 b0 b1 ha0 ha1 hb0 hb1
      hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda
      habound0 habound1 hsource t q)⟩

theorem exists_stackPlacedProfileChart_common_germ
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (delta : ℝ) (hdelta : 0 < delta)
    (W : Set E2) (hW : IsOpen W) (hcircle : sphere (0 : E2) 1 ⊆ W)
    (ha0near : ∀ v, |v| < delta → a0 v = (Real.sqrt (1 - v ^ 2))⁻¹)
    (ha1near : ∀ v, |v| < delta → a1 v = (Real.sqrt (1 - v ^ 2))⁻¹)
    (hb0near : ∀ x ∈ W, b0 x = 1) (hb1near : ∀ x ∈ W, b1 x = 1) :
    ∃ O : Set (E2 × ℝ), ∃ N : Set E3,
      IsOpen O ∧ sphere (0 : E2) 1 ×ˢ ({0} : Set ℝ) ⊆ O ∧
      (∀ t p, p ∈ O → M t p = M 0 p) ∧
      N = T '' (T.source ∩ (P '' (M 0 '' O))) ∧
      IsOpen N ∧ T '' (sphere (0 : E2) 1 ×ˢ ({m + sigma * c} : Set ℝ)) ⊆ N ∧
      N ⊆ T.target ∧
      ∀ t y, y ∈ N → (t, y) ∈ (e).target ∧ chartTimeField e (t, y) = 0 := by
  obtain ⟨O, hO, hEO, hformula, hconstant⟩ :=
    exists_stackCapProfilePath_common_ambient_germ a0 a1 b0 b1
      delta hdelta W hW hcircle ha0near ha1near hb0near hb1near
  let F := flatCapDiffeomorph a0 b0 ha0 hb0
    (fun v => (hapos0 v).ne') (fun x => (hbpos0 x).ne')
  have hM0 : M 0 = F := by
    funext p
    simp only [stackCapProfilePath, stackProfileBlend_of_nonpos a0 a1 0 le_rfl,
      stackProfileBlend_of_nonpos b0 b1 0 le_rfl,
      F, flatCapDiffeomorph_apply]
  have hMO : IsOpen (M 0 '' O) := by
    rw [hM0]
    exact F.toHomeomorph.isOpenMap O hO
  let N : Set E3 := T '' (T.source ∩ (P '' (M 0 '' O)))
  have hN : IsOpen N :=
    T.isOpen_image_source_inter ((P).toHomeomorph.isOpenMap _ hMO)
  have hNtarget : N ⊆ T.target := by
    rintro y ⟨z, hz, rfl⟩
    exact T.map_source hz.1
  have hseam : T '' (sphere (0 : E2) 1 ×ˢ ({m + sigma * c} : Set ℝ)) ⊆ N := by
    rintro y ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    have hz0 : z = m + sigma * c := mem_singleton_iff.mp hz
    subst z
    have hpO : (x, (0 : ℝ)) ∈ O := hEO ⟨hx, mem_singleton _⟩
    refine ⟨(x, m + sigma * c), ⟨hsource ⟨?_, mem_univ _⟩, ?_⟩, rfl⟩
    · exact mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp hx).le
    · refine ⟨M 0 (x, 0), ⟨(x, 0), hpO, rfl⟩, ?_⟩
      rw [hformula 0 (x, 0) hpO]
      simp only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, Real.sqrt_one,
        inv_one, one_smul, surgeryCapPlacementDiffeomorph_apply, mul_zero, add_zero]
  have he := (stackPlacedProfileChart_contDiffOn a0 a1 b0 b1 ha0 ha1 hb0 hb1
    hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda hsigma hlambda hT hTi).1
  refine ⟨O, N, hO, hEO, hconstant, rfl, hN, hseam, hNtarget, ?_⟩
  rintro t y ⟨z, ⟨hzT, ⟨w, ⟨p, hp, rfl⟩, rfl⟩⟩, rfl⟩
  have hpSource : (t, heightCoordinates.symm p) ∈ (e).source := by
    rw [stackPlacedProfileChart_source]
    simpa only [mem_ofPred_eq, heightCoordinates.apply_symm_apply, hconstant t p hp]
      using hzT
  have heq (s : ℝ) : e (s, heightCoordinates.symm p) = (s, T (P (M 0 p))) := by
    rw [stackPlacedProfileChart_apply, heightCoordinates.apply_symm_apply,
      hconstant s p hp]
  refine ⟨?_, ?_⟩
  · rw [stackPlacedProfileChart_target]
    exact ⟨mem_univ _, T.map_source hzT⟩
  · have hd := chartTimeField_track e he
      (fun z _ => stackPlacedProfileChart_time a0 a1 b0 b1 ha0 ha1 hb0 hb1
        hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda hsigma hlambda z)
      t (heightCoordinates.symm p) hpSource
    have hdconst : HasDerivAt (fun _ : ℝ => T (P (M 0 p)))
        (chartTimeField e (t, T (P (M 0 p)))) t := by
      simpa only [heq] using hd
    exact hdconst.unique (hasDerivAt_const t _)

include ha0 ha1 hb0 hb1 hapos0 hapos1 hbpos0 hbpos1 in

theorem stackPlacedProfileCap_signed_height
    (habound0 : ∀ v, |v| < 1 → a0 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (habound1 : ∀ v, |v| < 1 → a1 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (u : UnitTwoSphere)
    (hheight : ∀ p ∈ T.source, inner ℝ (u : E3) (T p) = p.2)
    (hsign : |sigma| = 1) (t : ℝ) (q : UnitTwoSphere) :
    sigma * (inner ℝ (u : E3) (cap t q) - (m + sigma * c)) =
      lambda * (M t (heightCoordinates (q : E3))).2 := by
  have hp := stackPlacedProfileCoordinates_mem_source a0 a1 b0 b1 ha0 ha1 hb0 hb1
    hapos0 hapos1 hbpos0 hbpos1 T m sigma c lambda
    habound0 habound1 hsource t q
  have hsquare : sigma * sigma = 1 := by nlinarith [sq_abs sigma]
  change sigma * (inner ℝ (u : E3)
    (T ((M t (heightCoordinates (q : E3))).1,
      m + sigma * (c + lambda * (M t (heightCoordinates (q : E3))).2))) -
        (m + sigma * c)) = _
  rw [hheight _ hp]
  calc
    sigma * ((m + sigma * (c + lambda * (M t (heightCoordinates (q : E3))).2)) -
        (m + sigma * c)) =
        (sigma * sigma) * (lambda * (M t (heightCoordinates (q : E3))).2) := by ring
    _ = lambda * (M t (heightCoordinates (q : E3))).2 := by rw [hsquare, one_mul]

end PoincareConjecture.M25.Topology3D
