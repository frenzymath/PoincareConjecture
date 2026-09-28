import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Collars.CollarNormalLabel

set_option autoImplicit false

open Set SignType Filter Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

variable {X P B C ι : Type*} [TopologicalSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace B] [TopologicalSpace C]

private theorem exists_positive_of_eventually {Q : ℝ → Prop}
    (hQ : ∀ᶠ t in 𝓝 (0 : ℝ), Q t) : ∃ t, 0 < t ∧ Q t := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hQ
  refine ⟨r / 2, by linarith, hball ?_⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_of_pos (by linarith : 0 < r / 2)]
  linarith

omit [NormedSpace ℝ P] in
private theorem PositiveCollarSignAt.eventually_positive
    {E : ι → OpenPartialHomeomorph X (P × ℝ)} {F : B × ℝ → X}
    {p : B} {s : SignType} (hs : PositiveCollarSignAt E F p s) :
    ∃ i, F (p, 0) ∈ (E i).source ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t → sign (E i (F (p, t))).2 = s := by
  obtain ⟨_, i, W, _, hpW, r, hr, hbase, hsign⟩ := hs
  refine ⟨i, hbase p hpW, ?_⟩
  filter_upwards [Iio_mem_nhds hr] with t ht hpos
  exact hsign p hpW t ⟨hpos, ht⟩

omit [NormedSpace ℝ P] in
private theorem path_sign_of_normal_coordinate
    (T E : OpenPartialHomeomorph X (P × ℝ))
    (F : ℝ → X) (hF : ContinuousAt F 0)
    (hT : F 0 ∈ T.source) (q : P) (hq : T (F 0) = (q, 0))
    (s v : SignType) (hs : BrownCollar.NormalSignAt (T.symm.trans E) q s)
    (κ : ℝ) (hheight : ∀ᶠ t in 𝓝 (0 : ℝ), (T (F t)).2 = κ * t)
    (hv : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t → sign (E (F t)).2 = v) :
    v = s * sign κ := by
  obtain ⟨_, U, hU, hqU, _, hsign⟩ := hs
  have hTF : ContinuousAt (fun t => T (F t)) 0 :=
    (T.continuousAt hT).comp hF
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ), T (F t) ∈ U :=
    hTF.preimage_mem_nhds (hU.mem_nhds (hq.symm ▸ hqU))
  have hsource : ∀ᶠ t in 𝓝 (0 : ℝ), F t ∈ T.source :=
    hF.preimage_mem_nhds (T.open_source.mem_nhds hT)
  obtain ⟨t, ht, htu, hts, hth, htv⟩ :=
    exists_positive_of_eventually (htarget.and (hsource.and (hheight.and hv)))
  have he := hsign (T (F t)) htu
  change sign (E (T.symm (T (F t)))).2 = s * sign (T (F t)).2 at he
  rw [T.left_inv hts, hth, sign_mul, sign_pos ht, mul_one] at he
  exact (htv ht).symm.trans he

theorem positive_normal_labels_eq_of_tube_coordinates
    {S : Set X} (E : ι → OpenPartialHomeomorph X (P × ℝ))
    (hpair : ∀ i y, y ∈ (E i).source → (y ∈ S ↔ (E i y).2 = 0))
    (hcompat : ∀ i j (x : S), (x : X) ∈ (E i).source ∩ (E j).source →
      ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
        EqOn (fun y => sign (E i y).2) (fun y => sign (E j y).2) V)
    (T : OpenPartialHomeomorph X (P × ℝ))
    (hTpair : ∀ y ∈ T.source, y ∈ S ↔ (T y).2 = 0)
    (F : B × ℝ → X) (G : C × ℝ → X) (p : B) (q : C)
    (hF : ContinuousAt F (p, (0 : ℝ))) (hG : ContinuousAt G (q, (0 : ℝ)))
    (hbase : F (p, 0) = G (q, 0)) (hS : F (p, 0) ∈ S)
    (hT : F (p, 0) ∈ T.source) (v w : SignType)
    (hv : PositiveCollarSignAt E F p v) (hw : PositiveCollarSignAt E G q w)
    (κ : ℝ)
    (hheightF : ∀ᶠ t in 𝓝 (0 : ℝ), (T (F (p, t))).2 = κ * t)
    (hheightG : ∀ᶠ t in 𝓝 (0 : ℝ), (T (G (q, t))).2 = t) :
    v = sign κ * w := by
  obtain ⟨i, hFi, hv⟩ := hv.eventually_positive
  obtain ⟨j, hGj, hw⟩ := hw.eventually_positive
  have hGi : G (q, 0) ∈ (E i).source := hbase ▸ hFi
  have hGS : G (q, 0) ∈ S := hbase ▸ hS
  obtain ⟨V, hV, hGV, heq⟩ := hcompat i j ⟨G (q, 0), hGS⟩ ⟨hGi, hGj⟩
  have hFp : ContinuousAt (fun t : ℝ => F (p, t)) 0 :=
    hF.comp (continuous_const.prodMk continuous_id).continuousAt
  have hGq : ContinuousAt (fun t : ℝ => G (q, t)) 0 :=
    hG.comp (continuous_const.prodMk continuous_id).continuousAt
  have hw' : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t → sign (E i (G (q, t))).2 = w := by
    filter_upwards [hGq.preimage_mem_nhds (hV.mem_nhds hGV), hw] with t ht hwt hpos
    exact (heq ht).trans (hwt hpos)
  let a := (T (F (p, 0))).1
  have ha : T (F (p, 0)) = (a, (0 : ℝ)) :=
    Prod.ext rfl ((hTpair _ hT).mp hS)
  have hat : (a, (0 : ℝ)) ∈ T.target := ha ▸ T.map_source hT
  have hai : T.symm (a, (0 : ℝ)) ∈ (E i).source := by
    rw [← ha, T.left_inv hT]
    exact hFi
  have htrans : ∀ z ∈ (T.symm.trans (E i)).source,
      ((T.symm.trans (E i)) z).2 = 0 ↔ z.2 = 0 := by
    intro z hz
    change (E i (T.symm z)).2 = 0 ↔ z.2 = 0
    calc
      _ ↔ T.symm z ∈ S := (hpair i (T.symm z) hz.2).symm
      _ ↔ (T (T.symm z)).2 = 0 := hTpair (T.symm z) (T.map_target hz.1)
      _ ↔ z.2 = 0 := by rw [T.right_inv hz.1]
  obtain ⟨s, hs⟩ := BrownCollar.exists_normalSignAt (T.symm.trans (E i)) htrans a ⟨hat, hai⟩
  have hvs := path_sign_of_normal_coordinate T (E i) (fun t => F (p, t))
    hFp hT a ha s v hs κ hheightF hv
  have hws := path_sign_of_normal_coordinate T (E i) (fun t => G (q, t))
    hGq (hbase ▸ hT) a (hbase ▸ ha) s w hs 1
    (by simpa only [one_mul] using hheightG) hw'
  simp only [sign_one, mul_one] at hws
  rw [hvs, hws, mul_comm]

end PoincareConjecture.M76.Dehn.Annuli.RimBands
