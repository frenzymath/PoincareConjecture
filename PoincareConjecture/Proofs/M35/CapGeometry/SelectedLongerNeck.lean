import PoincareConjecture.Proofs.M35.Thm12_28.SelectedStandardNeck

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem blowupSequence_longer_standard_evolving_neck
    (P : M35StandardCapPredecessors) (atlas : StandardCylinderAtlas)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (g : RiemannianMetric 3 L.limit.sliceCarrier.carrier) (N : EpsilonNeck g)
      (_hcenter : N.center = L.limit.base)
      (j : ℕ) (_hstage : closure N.carrier ⊆ L.exhaustion.space j)
      (delta epsilon : ℝ) (_hd : 0 < delta) (_he : 0 < epsilon)
      (_hehalf : epsilon < 1 / 2) (_hNd : N.epsilon ≤ delta)
      (_hde : delta ≤ epsilon / 4)
      (_hclose : RoundCylinderFamilyClose delta (Ioc (-(1 + epsilon)) 0)
        (fun u => roundCylinderPullback (L.limit.flow.metric u) N.coordinate_map)),
      ∀ᶠ k in atTop, Nonempty (StandardEvolvingNeck atlas E.flow (t (L.subsequence k))
        epsilon (x (L.subsequence k)) (Ioc (-(1 + epsilon)) 0)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro g N hcenter j hstage delta epsilon hd he hehalf hNd hde hclose
  have hsubDomain : (univ : Set UnitTwoSphere) ×ˢ Ioo (-delta⁻¹) delta⁻¹ ⊆
      univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    prod_mono subset_rfl (Ioo_subset_Ioo
      (neg_le_neg (inv_anti₀ N.epsilon_pos hNd)) (inv_anti₀ N.epsilon_pos hNd))
  have hspace : MapsTo N.coordinate_map (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹)
      (L.exhaustion.space j) := fun _ hz =>
    hstage (subset_closure (N.coordinatePartialDiffeomorph.map_source (hsubDomain hz)))
  obtain ⟨K, hK⟩ := blowupSequence_neck_family_close P E t x ht hR L N.coordinate_map
    delta epsilon hd he hde (N.coordinate_map_smooth.mono hsubDomain) j hspace
    (Ioc (-(1 + epsilon)) 0) (Icc (-(1 + epsilon)) 0) isCompact_Icc
    (fun _ hu => hu.2) (fun _ hu => ⟨hu.1.le, hu.2⟩) hclose
  have htime := L.exhaustion.time_cofinal (Icc (-(1 + epsilon)) 0) isCompact_Icc (by
    intro u hu
    simpa [blowupBackwardInterval] using hu.2)
  filter_upwards [eventually_ge_atTop j, eventually_ge_atTop K, htime] with k hj hk htk
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : Q = (E.flow.connection (t (L.subsequence k))).scalarCurvature
      (x (L.subsequence k)) := blowupSequence_scale P E t x ht hR (L.subsequence k)
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  have htime₀ : t (L.subsequence k) + 0 / Q ∈ Ico 0 E.flow.base.lifetime :=
    ((L.embedding k).forward 0 hzero L.limit.base).property
  let f := cylinderSpatialCoordinates E.flow.base.flow (L.embedding k)
    (L.exhaustion.space_open k) 0 hzero htime₀
  have hsub : N.carrier ⊆ f.source := fun _ hy =>
    L.exhaustion.space_increasing hj (hstage (subset_closure hy))
  have hbase : f L.limit.base = x (L.subsequence k) := by
    have hb := L.base_preserving k hzero
    exact congrArg (fun p : (generalizedFlow E.flow.base.flow).point => p.2.val) hb
  have hNe : N.epsilon ≤ epsilon := hNd.trans (hde.trans (by linarith))
  let patch₀ := (N.transportedStandardPatch f hsub).restrict
    (inv_pos.mpr he) (inv_anti₀ N.epsilon_pos hNe)
  let patch : StandardCylinderPatch epsilon⁻¹ (x (L.subsequence k)) :=
    { patch₀ with
      center_sphere := by
        obtain ⟨q, hq⟩ := patch₀.center_sphere
        exact ⟨q, hq.trans ((congrArg f hcenter).trans hbase)⟩ }
  refine ⟨{
    time_mem := ht (L.subsequence k)
    epsilon_pos := he
    epsilon_lt_half := hehalf
    scalar_pos := E.scalar_pos (ht (L.subsequence k)) (x (L.subsequence k))
    patch := patch
    interval_survival := ?_
    close := ?_
  }⟩
  · intro u hu
    have h := ((L.embedding k).forward u (htk ⟨hu.1.le, hu.2⟩) L.limit.base).property
    change t (L.subsequence k) + u / Q ∈ Ico 0 E.flow.base.lifetime at h
    rwa [hQ] at h
  · have h := hK k hk
    change RoundCylinderFamilyClose epsilon (Ioc (-(1 + epsilon)) 0)
      (fun u z v w => Q * roundCylinderPullback
        (E.flow.metric (t (L.subsequence k) + u / Q)) patch.coordinate z v w) at h
    change RoundCylinderFamilyClose epsilon (Ioc (-(1 + epsilon)) 0)
      (fun u z v w => (E.flow.connection (t (L.subsequence k))).scalarCurvature
        (x (L.subsequence k)) * roundCylinderPullback
          (E.flow.metric (t (L.subsequence k) + u /
            (E.flow.connection (t (L.subsequence k))).scalarCurvature (x (L.subsequence k))))
          patch.coordinate z v w)
    rwa [hQ] at h

end PoincareConjecture.M35.OrdinaryRealization
