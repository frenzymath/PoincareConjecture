import PoincareConjecture.Proofs.M25.AppA_1_Necks.SliceProjectionDifferential
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.CollarAbsorption

set_option autoImplicit false

open Set PoincareConjecture.M25.Topology3D
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_positive_quarter_sphere_coordinate_adjustment :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier →
      ∃ (A : Diffeomorph (𝓡 2) (𝓡 2)
          UnitTwoSphere UnitTwoSphere ∞)
        (e : OpenPartialHomeomorph RoundCylinderSpace M),
        e.source = N.cylinderDomain ∧ e.target = N.carrier ∧
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e
          N.cylinderDomain ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm
          N.carrier ∧
        (∀ z ∈ N.cylinderDomain,
          (N.coordinate_inverse (e z)).2 = z.2) ∧
        (∀ x ∈ N.carrier,
          (e.symm x).2 = (N.coordinate_inverse x).2) ∧
        (∀ z ∈ N.cylinderDomain, z.2 ≤ 5 * N.epsilon⁻¹ / 8 →
          e z = N.coordinate_map z) ∧
        (∀ x ∈ N.carrier,
          (N.coordinate_inverse x).2 ≤ 5 * N.epsilon⁻¹ / 8 →
          e.symm x = N.coordinate_inverse x) ∧
        (∀ q : UnitTwoSphere,
          A q = (N'.coordinate_inverse
            (N.coordinate_map (q, 5 * N.epsilon⁻¹ / 8))).1) ∧
        (∀ z : RoundCylinderSpace,
          z.2 ∈ Icc (11 * N.epsilon⁻¹ / 16) (13 * N.epsilon⁻¹ / 16) →
          e z ∈ N'.carrier ∧ (N'.coordinate_inverse (e z)).1 = A z.1) ∧
        (∀ x ∈ N.carrier,
          (N.coordinate_inverse x).2 ∈
            Icc (11 * N.epsilon⁻¹ / 16) (13 * N.epsilon⁻¹ / 16) →
          x ∈ N'.carrier ∧
            (e.symm x).1 = A.symm (N'.coordinate_inverse x).1) := by
  classical
  obtain ⟨epsilon0, hepos, hecap, htrans⟩ :=
    exists_intersecting_axial_transversality.{u}
  refine ⟨epsilon0, hepos, hecap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' hquarter
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (n := 2) (by norm_num)
  let L := N.epsilon⁻¹
  let a := 5 * L / 8
  let b := 11 * L / 16
  let c := 13 * L / 16
  let d := 7 * L / 8
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  have hLa : L / 2 < a := by dsimp only [a]; linarith
  have ha : 0 < a := by dsimp only [a]; positivity
  have hab : a < b := by dsimp only [a, b]; linarith
  have hbc : b < c := by dsimp only [b, c]; linarith
  have hcd : c < d := by dsimp only [c, d]; linarith
  have hdL : d < L := by dsimp only [d]; linarith
  have had : a ≤ d := (hab.trans (hbc.trans hcd)).le
  have hstrip {t : ℝ} (ht : t ∈ Icc a d) :
      t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨by change -L < t; linarith [ht.1], ht.2.trans_lt hdL⟩
  have hnext (t : ℝ) (ht : t ∈ Icc a d) (q : UnitTwoSphere) :
      N.coordinate_map (q, t) ∈ N'.carrier := by
    have hz : (q, t) ∈ N.cylinderDomain := ⟨mem_univ _, hstrip ht⟩
    apply hquarter
    refine ⟨N.coordinate_map_mem hz, ?_, ?_⟩
    · rw [N.coordinate_inverse_coordinate_map hz]
      exact hLa.trans_le ht.1
    · rw [N.coordinate_inverse_coordinate_map hz]
      exact (hstrip ht).2
  let F (t : ℝ) (q : UnitTwoSphere) :=
    (N'.coordinate_inverse (N.coordinate_map (q, t))).1
  have hlocal (t : ℝ) (ht : t ∈ Icc a d) :
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (F t) := by
    apply N'.slice_projection_isLocalDiffeomorph_of_transverse N
      (hstrip ht) (hnext t ht)
    intro q
    exact (htrans N N' hN hN' (N.coordinate_map (q, t))
      (N.coordinate_map_mem ⟨mem_univ _, hstrip ht⟩) (hnext t ht q)).2
  let Ft (t : ℝ) (ht : t ∈ Icc a d) :=
    Poincare.Geometry.Manifold.sphereDiffeomorphOfLocalDiffeomorph
      (n := 0) (F t) (hlocal t ht)
  let A := Ft a ⟨le_rfl, had⟩
  have hA (q : UnitTwoSphere) : A q = F a q := rfl
  let u (s : ℝ) := collarCutoff a b s
  let v (s : ℝ) := collarCutoff c d s
  let rho (s : ℝ) := (1 - u s) * a + u s * ((1 - v s) * s + v s * d)
  have hu (s : ℝ) : 0 ≤ u s ∧ u s ≤ 1 := collarCutoff_mem_Icc a b s
  have hv (s : ℝ) : 0 ≤ v s ∧ v s ≤ 1 := collarCutoff_mem_Icc c d s
  have hrho : ContDiff ℝ ∞ rho :=
    ((contDiff_const.sub (contDiff_collarCutoff a b)).mul contDiff_const).add
      ((contDiff_collarCutoff a b).mul
        (((contDiff_const.sub (contDiff_collarCutoff c d)).mul contDiff_id).add
          ((contDiff_collarCutoff c d).mul contDiff_const)))
  have hrholower {s : ℝ} (hs : s ≤ a) : rho s = a := by
    have hzero : u s = 0 := collarCutoff_eq_zero hab hs
    dsimp only [rho]
    rw [hzero]
    ring
  have hrhoupper {s : ℝ} (hs : d ≤ s) : rho s = d := by
    have huone : u s = 1 := collarCutoff_eq_one hab ((hbc.trans hcd).le.trans hs)
    have hvone : v s = 1 := collarCutoff_eq_one hcd hs
    dsimp only [rho]
    rw [huone, hvone]
    ring
  have hrhomiddle {s : ℝ} (hs : s ∈ Icc b c) : rho s = s := by
    have huone : u s = 1 := collarCutoff_eq_one hab hs.1
    have hvzero : v s = 0 := collarCutoff_eq_zero hcd hs.2
    dsimp only [rho]
    rw [huone, hvzero]
    ring
  have hrhomem (s : ℝ) : rho s ∈ Icc a d := by
    by_cases hsa : s ≤ a
    · rw [hrholower hsa]
      exact ⟨le_rfl, had⟩
    by_cases hds : d ≤ s
    · rw [hrhoupper hds]
      exact ⟨had, le_rfl⟩
    have has : a ≤ s := (lt_of_not_ge hsa).le
    have hsd : s ≤ d := (lt_of_not_ge hds).le
    by_cases hsc : s ≤ c
    · have hvzero : v s = 0 := collarCutoff_eq_zero hcd hsc
      dsimp only [rho]
      rw [hvzero]
      simp only [sub_zero, one_mul, zero_mul, add_zero]
      constructor
      · nlinarith [mul_nonneg (hu s).1 (sub_nonneg.mpr has)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr (hu s).2) (sub_nonneg.mpr had),
          mul_nonneg (hu s).1 (sub_nonneg.mpr hsd)]
    · have huone : u s = 1 :=
        collarCutoff_eq_one hab (hbc.le.trans (lt_of_not_ge hsc).le)
      dsimp only [rho]
      rw [huone]
      simp only [sub_self, zero_mul, one_mul, zero_add]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr (hv s).2) (sub_nonneg.mpr has),
          mul_nonneg (hv s).1 (sub_nonneg.mpr had)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr (hv s).2) (sub_nonneg.mpr hsd)]
  let G (s : ℝ) (q : UnitTwoSphere) := A.symm (F (rho s) q)
  have hp : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × UnitTwoSphere => (p.2, rho p.1)) :=
    contMDiff_snd.prodMk (hrho.contMDiff.comp contMDiff_fst)
  have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞
      (fun p : ℝ × UnitTwoSphere => N.coordinate_map (p.2, rho p.1)) :=
    N.coordinate_map_smooth.comp_contMDiff hp
      (fun p => ⟨mem_univ _, hstrip (hrhomem p.1)⟩)
  have hcoord : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × UnitTwoSphere =>
        N'.coordinate_inverse (N.coordinate_map (p.2, rho p.1))) :=
    N'.coordinate_inverse_smooth.comp_contMDiff hmap
      (fun p => hnext (rho p.1) (hrhomem p.1) p.2)
  have hG : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => G p.1 p.2) :=
    A.symm.contMDiff.comp (contMDiff_fst.comp hcoord)
  have hGt (s : ℝ) : ∃ e : Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞, ∀ q, e q = G s q :=
    ⟨(Ft (rho s) (hrhomem s)).trans A.symm, fun _ => rfl⟩
  let D := sphereIsotopyAbsorption hG hGt id contDiff_id
  have hD (z : RoundCylinderSpace) : D z = (A.symm (F (rho z.2) z.1), z.2) := rfl
  have hDsnd (z : RoundCylinderSpace) : (D z).2 = z.2 := rfl
  have hDisnd (z : RoundCylinderSpace) : (D.symm z).2 = z.2 := rfl
  have hDlower (z : RoundCylinderSpace) (hz : z.2 ≤ a) : D z = z := by
    rw [hD, hrholower hz, ← hA, A.symm_apply_apply]
  have hDilower (z : RoundCylinderSpace) (hz : z.2 ≤ a) : D.symm z = z := by
    calc
      D.symm z = D.symm (D z) := congrArg D.symm (hDlower z hz).symm
      _ = z := D.symm_apply_apply z
  have hDidom {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain) :
      D.symm z ∈ N.cylinderDomain := by
    exact ⟨mem_univ _, by rw [hDisnd]; exact hz.2⟩
  let e := D.symm.toHomeomorph.toOpenPartialHomeomorph.trans N.coordinatePartialHomeomorph
  have he (z : RoundCylinderSpace) : e z = N.coordinate_map (D.symm z) := rfl
  have hei (x : M) : e.symm x = D (N.coordinate_inverse x) := rfl
  have hsource : e.source = N.cylinderDomain := by
    dsimp only [e]
    rw [OpenPartialHomeomorph.trans_source]
    ext z
    change (z ∈ (univ : Set RoundCylinderSpace) ∧ D.symm z ∈ N.cylinderDomain) ↔
      z ∈ N.cylinderDomain
    simp only [mem_univ, true_and]
    change ((D.symm z).1 ∈ (univ : Set UnitTwoSphere) ∧
      (D.symm z).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ↔
        (z.1 ∈ (univ : Set UnitTwoSphere) ∧ z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    rw [hDisnd]
    simp only [mem_univ, true_and]
  have htarget : e.target = N.carrier := by
    dsimp only [e]
    rw [OpenPartialHomeomorph.trans_target]
    ext x
    change (x ∈ N.carrier ∧ N.coordinate_inverse x ∈ (univ : Set RoundCylinderSpace)) ↔
      x ∈ N.carrier
    simp only [mem_univ, and_true]
  have hesmooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e
      N.cylinderDomain :=
    N.coordinate_map_smooth.comp D.symm.contMDiff.contMDiffOn (fun _ hz => hDidom hz)
  have heismooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm N.carrier :=
    D.contMDiff.comp_contMDiffOn N.coordinate_inverse_smooth
  refine ⟨A, e, hsource, htarget, hesmooth, heismooth, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [he, N.coordinate_inverse_coordinate_map (hDidom hz)]
    exact hDisnd z
  · intro x _
    rw [hei]
    exact hDsnd (N.coordinate_inverse x)
  · intro z _ hz
    rw [he, hDilower z hz]
  · intro x _ hx
    rw [hei, hDlower (N.coordinate_inverse x) hx]
  · exact hA
  · intro z hz
    have hw : (D.symm z).2 ∈ Icc a d := by
      rw [hDisnd]
      exact ⟨hab.le.trans hz.1, hz.2.trans hcd.le⟩
    have hn := hnext (D.symm z).2 hw (D.symm z).1
    refine ⟨?_, ?_⟩
    · simpa only [he, Prod.mk.eta] using hn
    · have hfirst := congrArg Prod.fst (D.apply_symm_apply z)
      change A.symm (F (rho (D.symm z).2) (D.symm z).1) = z.1 at hfirst
      have hwband : (D.symm z).2 ∈ Icc b c := by rw [hDisnd]; exact hz
      rw [hrhomiddle hwband] at hfirst
      have hfirst' := congrArg A hfirst
      rw [A.apply_symm_apply] at hfirst'
      change F (D.symm z).2 (D.symm z).1 = A z.1
      exact hfirst'
  · intro x hx hband
    have ht : (N.coordinate_inverse x).2 ∈ Icc a d :=
      ⟨hab.le.trans hband.1, hband.2.trans hcd.le⟩
    have hn := hnext (N.coordinate_inverse x).2 ht (N.coordinate_inverse x).1
    refine ⟨?_, ?_⟩
    · simpa only [Prod.mk.eta, N.coordinate_map_coordinate_inverse hx] using hn
    · rw [hei, hD]
      change A.symm (F (rho (N.coordinate_inverse x).2) (N.coordinate_inverse x).1) = _
      rw [hrhomiddle hband]
      simp only [F, Prod.mk.eta, N.coordinate_map_coordinate_inverse hx]

end PoincareConjecture.EpsilonNeck
