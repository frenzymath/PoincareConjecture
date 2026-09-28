import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRecentPaths
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCenterMargin
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialJoiningHeightPath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

section StandardGeometry

variable {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
  {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
  (N : StandardEvolvingNeck atlas G v gamma z
    (Icc (-v * (G.connection v).scalarCurvature z) 0))
  (hsmall : gamma ≤ 1 / 1200)
  (hdisjoint : Disjoint N.patch.carrier
    {y | g0.metric.edist 0 y ≤ ENNReal.ofReal (g0.cylindrical_end.radius + 4)})
  (hshort : v * (G.connection v).scalarCurvature z < 1 + gamma)

include hsmall hdisjoint hshort

theorem exists_standard_initial_neck_half_strip_paths
    {x y : StandardCapSpace} (hx : x ∈ N.patch.carrier)
    (hheight : |(N.patch.inverse x).2| ≤ 1)
    (hy : y ∈ N.patch.coordinate '' (univ ×ˢ Ioo (-gamma⁻¹ / 2) (gamma⁻¹ / 2))) :
    ∃ p₁ p₂ : ℝ → StandardCapSpace,
      p₁ 0 = x ∧ p₁ 1 = p₂ 0 ∧ p₂ 1 = y ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p₁ (Icc 0 1) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p₂ (Icc 0 1) ∧
      MapsTo p₁ (Icc (0 : ℝ) 1)
        (N.patch.coordinate '' (univ ×ˢ Ioo (-gamma⁻¹ / 2) (gamma⁻¹ / 2))) ∧
      MapsTo p₂ (Icc (0 : ℝ) 1)
        (N.patch.coordinate '' (univ ×ˢ Ioo (-gamma⁻¹ / 2) (gamma⁻¹ / 2))) ∧
      g0.metric.pathELength p₁ 0 1 + g0.metric.pathELength p₂ 0 1 <
        ENNReal.ofReal ((51 / 50 : ℝ) * (7 + gamma⁻¹ / 2)) := by
  have hL : (1200 : ℝ) ≤ gamma⁻¹ := by
    have h := inv_anti₀ N.epsilon_pos hsmall
    norm_num at h
    exact h
  rcases hy with ⟨⟨q, a⟩, ⟨_, ha⟩, rfl⟩
  have hxhalf : (N.patch.inverse x).2 ∈ Ioo (-(gamma⁻¹ / 2)) (gamma⁻¹ / 2) := by
    apply abs_lt.mp
    linarith only [hheight, hL]
  have ha' : a ∈ Ioo (-(gamma⁻¹ / 2)) (gamma⁻¹ / 2) := by
    simpa only [neg_div] using ha
  obtain ⟨p₁, p₂, hp10, hp11, hp20, hp21, hp₁, hp₂, hmem₁, hmem₂, hlen⟩ :=
    exists_standard_initial_neck_strip_paths N hsmall hdisjoint hshort
      (R := gamma⁻¹ / 2) (by linarith only [hL])
      (N.patch.inverse x).1 q hxhalf ha'
  have hpx : N.patch.coordinate ((N.patch.inverse x).1, (N.patch.inverse x).2) = x :=
    N.patch.coordinate_right_inverse hx
  refine ⟨p₁, p₂, hp10.trans hpx, hp11.trans hp20.symm, hp21, hp₁, hp₂,
    ?_, ?_, ?_⟩
  · simpa only [neg_div] using hmem₁
  · simpa only [neg_div] using hmem₂
  apply hlen.trans_le
  apply ENNReal.ofReal_le_ofReal
  have haabs : |a| < gamma⁻¹ / 2 := abs_lt.mpr ha'
  have hdiff : |a - (N.patch.inverse x).2| ≤ gamma⁻¹ / 2 + 1 :=
    (abs_sub _ _).trans (add_le_add haabs.le hheight)
  linarith only [hdiff]

theorem standard_initial_neck_half_strip_tip_distance
    {x : StandardCapSpace} (hx : x ∈ N.patch.carrier)
    (hheight : |(N.patch.inverse x).2| ≤ 1)
    {y : StandardCapSpace}
    (hy : y ∈ N.patch.coordinate '' (univ ×ˢ Ioo (-gamma⁻¹ / 2) (gamma⁻¹ / 2))) :
    ENNReal.ofReal (g0.cylindrical_end.radius + 104) ≤ g0.metric.edist 0 y := by
  obtain ⟨p₁, p₂, hp10, hpjoin, hp21, hp₁, hp₂, _hmem₁, _hmem₂, hlen⟩ :=
    exists_standard_initial_neck_half_strip_paths N hsmall hdisjoint hshort hx hheight hy
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g0.metric.toRiemannianMetric⟩
  have hdist : g0.metric.edist x y <
      ENNReal.ofReal ((51 / 50 : ℝ) * (7 + gamma⁻¹ / 2)) := by
    calc
      _ ≤ g0.metric.edist x (p₁ 1) + g0.metric.edist (p₁ 1) y :=
        Manifold.riemannianEDist_triangle
      _ ≤ g0.metric.pathELength p₁ 0 1 + g0.metric.pathELength p₂ 0 1 :=
        add_le_add (M13.edist_le_pathELength _ hp₁ hp10 rfl zero_le_one)
          (M13.edist_le_pathELength _ hp₂ hpjoin.symm hp21 zero_le_one)
      _ < _ := hlen
  have hL : (1200 : ℝ) ≤ gamma⁻¹ := by
    have h := inv_anti₀ N.epsilon_pos hsmall
    norm_num at h
    exact h
  have hfar := standard_initial_neck_tip_distance_sharp N hsmall hdisjoint hshort hx hheight
  have hfarReal := (ENNReal.ofReal_le_iff_le_toReal (g0.metric.edist_ne_top 0 x)).mp hfar
  have hdistReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist.le
  rw [ENNReal.toReal_ofReal (by linarith only [hL])] at hdistReal
  have htriangle : g0.metric.edist 0 x ≤ g0.metric.edist 0 y + g0.metric.edist x y := by
    have ht : g0.metric.edist 0 x ≤ g0.metric.edist 0 y + g0.metric.edist y x :=
      Manifold.riemannianEDist_triangle
    have hc : g0.metric.edist y x = g0.metric.edist x y := Manifold.riemannianEDist_comm
    rwa [hc] at ht
  have htriangleReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨g0.metric.edist_ne_top 0 y, g0.metric.edist_ne_top x y⟩) htriangle
  rw [ENNReal.toReal_add (g0.metric.edist_ne_top 0 y) (g0.metric.edist_ne_top x y)] at htriangleReal
  apply (ENNReal.ofReal_le_iff_le_toReal (g0.metric.edist_ne_top 0 y)).mpr
  linarith only [hfarReal, hdistReal, htriangleReal, hL]

end StandardGeometry

theorem exists_source_initial_recent_geometry_tolerance
    (g0 : StandardInitialMetric) (gamma : ℝ)
    (hgamma : 0 < gamma) (hsmall : gamma ≤ 1 / 1200) :
    ∃ eta0 delta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 / 1000 ∧ 0 < delta0 ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
      ∀ (i : Fin (F.event t hT).cap_count)
        (S : MaximalStandardCapFlow F.standard_initial) (A eta : ℝ) (J : Set ℝ)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
          ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
        (initial : SurgeryCapInitialComparison F t hT i A),
        SurgeryCapFamilyComparison F S A eta e initial.chart →
        ∀ hzero : (0 : ℝ) ∈ J,
          (∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
            HEq (e.forward 0 hzero y) y) →
          0 < eta → eta ≤ eta0 → ((F.event t hT).necks i).neck.epsilon ≤ delta0 →
        ∀ (atlas : StandardCylinderAtlas) (v : ℝ) (z : StandardCapSpace)
          (N : StandardEvolvingNeck atlas S v gamma z
            (Icc (-v * (S.connection v).scalarCurvature z) 0)),
          Disjoint N.patch.carrier
            {y | F.standard_initial.metric.edist 0 y ≤
              ENNReal.ofReal (F.standard_initial.cylindrical_end.radius + 4)} →
          v * (S.connection v).scalarCurvature z < 1 + gamma →
        let U := N.patch.coordinate '' (univ ×ˢ Ioo (-gamma⁻¹ / 2) (gamma⁻¹ / 2))
        U ⊆ F.standard_initial.metric.ball 0 A →
        ∀ x ∈ N.patch.carrier, |(N.patch.inverse x).2| ≤ 1 →
        let old := ((F.event t hT).necks i).neck
        let c := (old.coordinate_inverse (sourceInitialOldMap initial x)).2
        x ∈ U ∧ (∀ y ∈ U, initial.chart y ∉ ((F.event t hT).caps i).carrier) ∧
          c + 2 * gamma⁻¹ / 3 < 0 ∧
          MapsTo (sourceInitialOldMap initial) U
            (old.region (c - 2 * gamma⁻¹ / 3) (c + 2 * gamma⁻¹ / 3)) := by
  obtain ⟨Lambda, etaCenter, delta0, hLambda, hLambdaSmall, hetaCenter, hdelta0,
    hdelta, _hetaCenterBudget, centerMargin⟩ :=
    exists_source_initial_older_center_margin g0 gamma hgamma hsmall
  obtain ⟨etaAvoid, hetaAvoid, avoid⟩ := exists_source_initial_cap_avoidance_tolerance g0
  let eta0 := min etaCenter (min etaAvoid (1 / 1000))
  have heta0 : 0 < eta0 := lt_min hetaCenter (lt_min hetaAvoid (by norm_num))
  have heta0Small : eta0 ≤ 1 / 1000 := (min_le_right _ _).trans (min_le_right _ _)
  have hL : (1200 : ℝ) ≤ gamma⁻¹ := by
    have h := inv_anti₀ hgamma hsmall
    norm_num at h
    exact h
  refine ⟨eta0, delta0, heta0, heta0Small, hdelta0, ?_⟩
  intro F hinitial t hT hn i S A eta J e initial comparison hzero hbase
    heta hetaSmall hdeltaSmall atlas v z N hdisjoint hshort U hsource x hx hheight
  let old := ((F.event t hT).necks i).neck
  let c := (old.coordinate_inverse (sourceInitialOldMap initial x)).2
  have hU : IsOpen U := by
    simpa only [U, neg_div] using
      N.patch.open_axial_slab (show gamma⁻¹ / 2 ≤ gamma⁻¹ by linarith only [hL])
  have hxU : x ∈ U := by
    refine ⟨N.patch.inverse x, ⟨mem_univ _, ?_⟩, N.patch.coordinate_right_inverse hx⟩
    have h := abs_lt.mp (show |(N.patch.inverse x).2| < gamma⁻¹ / 2 by
      linarith only [hheight, hL])
    simpa only [neg_div, mem_Ioo] using h
  have hh : 0 < F.parameters.h t := (F.event t hT).neck_scale i ▸ old.scale_pos
  have havoid : ∀ y ∈ U, initial.chart y ∉ ((F.event t hT).caps i).carrier := by
    intro y hy
    exact avoid F hinitial t hT i S A eta J e initial comparison hzero hbase hh heta
      (hetaSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) y (hsource hy)
      (standard_initial_neck_half_strip_tip_distance N hsmall hdisjoint hshort hx hheight hy)
  have hcenter := centerMargin F hinitial t hT i S A eta J e initial comparison
    hzero hbase heta (hetaSmall.trans (min_le_left _ _)) hdeltaSmall
    atlas v z N hdisjoint hshort x (hsource hxU) hx hheight
  refine ⟨hxU, havoid, hcenter.2, ?_⟩
  intro y hy
  obtain ⟨p₁, p₂, hp10, hpjoin, hp21, hp₁, hp₂, hmem₁, hmem₂, hlen⟩ :=
    exists_standard_initial_neck_half_strip_paths N hsmall hdisjoint hshort hx hheight hy
  have hLambdaPos : 0 < Lambda := zero_lt_one.trans hLambda
  have hbudget := (hdelta old.epsilon old.epsilon_pos.le hdeltaSmall).2
  have hlen₁ := source_initial_joining_height_path_length e initial comparison hzero hbase
    heta (hetaSmall.trans heta0Small) hLambdaPos hbudget hU hsource havoid hp₁ hmem₁
  have hlen₂ := source_initial_joining_height_path_length e initial comparison hzero hbase
    heta (hetaSmall.trans heta0Small) hLambdaPos hbudget hU hsource havoid hp₂ hmem₂
  let f := fun w : StandardCapSpace => (old.coordinate_inverse (sourceInitialOldMap initial w)).2
  change edist (f (p₁ 0)) (f (p₁ 1)) ≤ _ at hlen₁
  change edist (f (p₂ 0)) (f (p₂ 1)) ≤ _ at hlen₂
  rw [hp10] at hlen₁
  rw [← hpjoin, hp21] at hlen₂
  have hheightBound : edist (f x) (f y) < ENNReal.ofReal (2 * gamma⁻¹ / 3) := by
    calc
      _ ≤ edist (f x) (f (p₁ 1)) + edist (f (p₁ 1)) (f y) := edist_triangle _ _ _
      _ ≤ ENNReal.ofReal ((101 / 100 : ℝ) * Lambda) *
          (F.standard_initial.metric.pathELength p₁ 0 1 +
            F.standard_initial.metric.pathELength p₂ 0 1) := by
        simpa only [mul_add] using add_le_add hlen₁ hlen₂
      _ < ENNReal.ofReal ((101 / 100 : ℝ) * Lambda) *
          ENNReal.ofReal ((51 / 50 : ℝ) * (7 + gamma⁻¹ / 2)) :=
        ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
          ENNReal.ofReal_ne_top hlen
      _ ≤ ENNReal.ofReal (2 * gamma⁻¹ / 3) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (101 / 100 : ℝ) * Lambda)]
        apply ENNReal.ofReal_le_ofReal
        have hmul := mul_le_mul_of_nonneg_right hLambdaSmall.le
          (show 0 ≤ (101 / 100 : ℝ) * ((51 / 50 : ℝ) * (7 + gamma⁻¹ / 2)) by
            linarith only [hL])
        nlinarith only [hmul, hL]
  rw [edist_dist, Real.dist_eq] at hheightBound
  have habs : |f y - c| < 2 * gamma⁻¹ / 3 := by
    have h : |f x - f y| < 2 * gamma⁻¹ / 3 :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hL])).mp hheightBound
    simpa only [c, f, abs_sub_comm] using h
  have hret := source_initial_chart_retention hT i initial (hsource hy) (havoid y hy)
  refine ⟨hret.2.2.1, ?_, ?_⟩
  · have h := (abs_lt.mp habs).1
    change c - 2 * gamma⁻¹ / 3 < f y
    linarith only [h]
  · have h := (abs_lt.mp habs).2
    change f y < c + 2 * gamma⁻¹ / 3
    linarith only [h]

end PoincareConjecture.M47
