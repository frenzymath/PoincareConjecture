import PoincareConjecture.Proofs.M28.Sec10_3_Tube.TubeNeckConfinement












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]






theorem exists_interior_endpoint_neck_confinement
    (g : RiemannianMetric 3 M) (V U : TopologicalSpace.Opens M)
    (A : OpenCylinderModel (V : Set M))
    (hU : (U : Set M) = A.tail true (1 / 2))
    (N : Bool → EpsilonNeck g)
    (hNU : ∀ i, (N i).carrier ⊆ (U : Set M))
    (fMinus fPlus : M → ℝ) {lambda bPlus : ℝ}
    (hlambda : lambda ∈ Ioo (1 / 2 : ℝ) 1)
    (hbPlus : bPlus ∈ Ioo (1 / 2 : ℝ) 1)
    (hfMinus : ContinuousOn fMinus (V : Set M))
    (hfPlus : ContinuousOn fPlus (V : Set M))
    (hzeroMinus : ∀ x ∈ V, fMinus x = 0 ↔ x ∈ (N false).central_sphere)
    (hzeroPlus : ∀ x ∈ V, fPlus x = 0 ↔ x ∈ (N true).central_sphere)
    (hbackHeight : ∀ x ∈ V, 0 ≤ fMinus x → lambda ≤ (A.inverse x).2)
    (hbackSlab : ∀ x ∈ (N false).coordinate_map ''
        (univ ×ˢ Icc (-((N false).epsilon⁻¹ / 2)) ((N false).epsilon⁻¹ / 2)),
      lambda ≤ (A.inverse x).2)
    (hfrontSlab : ∀ x ∈ (N true).coordinate_map ''
        (univ ×ˢ Icc (-((N true).epsilon⁻¹ / 2)) ((N true).epsilon⁻¹ / 2)),
      0 ≤ fMinus x)
    (hfrontHigh : ∀ x ∈ V, bPlus < (A.inverse x).2 → 0 < fPlus x)
    {p q : M} (hpV : p ∈ V) (hqV : q ∈ V)
    (hpMinus : 0 < fMinus p) (hqMinus : 0 < fMinus q)
    (hpPlus : fPlus p < 0) (hqPlus : fPlus q < 0) :
    ∃ (K : Set M) (B : ℝ), IsCompact K ∧ K ⊆ (U : Set M) ∧
      p ∈ K ∧ q ∈ K ∧
      (∀ x ∈ K, lambda ≤ (A.inverse x).2) ∧
      lambda < B ∧ B < 1 ∧ K ⊆ A.compactSlab lambda B ∧
      ∀ γ : ℝ → M, γ 0 = p → γ 1 = q →
        ContinuousOn γ (Icc (0 : ℝ) 1) →
        MapsTo γ (Icc (0 : ℝ) 1) (U : Set M) →
        ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ K →
          ∃ (i : Bool) (c d : ℝ), 0 ≤ c ∧ c ≤ t ∧ t ≤ d ∧ d ≤ 1 ∧
            γ c ∈ (N i).central_sphere ∧ γ d ∈ (N i).central_sphere ∧
            γ t ∉ (N i).region (-((N i).epsilon⁻¹ / 2)) ((N i).epsilon⁻¹ / 2) := by
  have hlambda0 : 0 < lambda := (by norm_num : (0 : ℝ) < 1 / 2).trans hlambda.1
  have hUV : (U : Set M) ⊆ (V : Set M) := by
    rw [hU]
    exact A.tail_subset_m28 true (by norm_num) (by norm_num)
  let Slab := A.compactSlab lambda bPlus
  have hSlab : IsCompact Slab := A.isCompact_compactSlab hlambda0 hbPlus.2
  have hSlabV : Slab ⊆ (V : Set M) := A.compactSlab_subset hlambda0 hbPlus.2
  let J := Slab ∩ fMinus ⁻¹' Ici (0 : ℝ)
  have hJclosed : IsClosed J :=
    (hfMinus.mono hSlabV).preimage_isClosed_of_isClosed hSlab.isClosed isClosed_Ici
  have hJ : IsCompact J := hSlab.of_isClosed_subset hJclosed inter_subset_left
  have hJV : J ⊆ (V : Set M) := inter_subset_left.trans hSlabV
  let Middle := J ∩ fPlus ⁻¹' Iic (0 : ℝ)
  have hMiddleClosed : IsClosed Middle :=
    (hfPlus.mono hJV).preimage_isClosed_of_isClosed hJclosed isClosed_Iic
  have hMiddle : IsCompact Middle := hJ.of_isClosed_subset hMiddleClosed inter_subset_left
  have hmiddleCapture {x : M} (hx : x ∈ V)
      (hminus : 0 ≤ fMinus x) (hplus : fPlus x ≤ 0) : x ∈ Middle := by
    refine ⟨⟨(A.mem_compactSlab_iff hlambda0 hbPlus.2).mpr
      ⟨hx, hbackHeight x hx hminus, ?_⟩, hminus⟩, hplus⟩
    exact le_of_not_gt (fun hhigh =>
      (not_lt_of_ge hplus) (hfrontHigh x hx hhigh))
  have hMiddleU : Middle ⊆ (U : Set M) := by
    intro x hx
    have hslab := (A.mem_compactSlab_iff hlambda0 hbPlus.2).mp hx.1.1
    rw [hU]
    exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
      ⟨hslab.1, hlambda.1.trans_le hslab.2.1⟩
  have hMiddleHeight (x : M) (hx : x ∈ Middle) :
      lambda ≤ (A.inverse x).2 :=
    ((A.mem_compactSlab_iff hlambda0 hbPlus.2).mp hx.1.1).2.1
  let D (i : Bool) := (N i).coordinate_map ''
    (univ ×ˢ Icc (-((N i).epsilon⁻¹ / 2)) ((N i).epsilon⁻¹ / 2))
  have hD (i : Bool) : IsCompact (D i) := by
    have hpos : 0 < (N i).epsilon⁻¹ := inv_pos.mpr (N i).epsilon_pos
    exact (N i).isCompact_coordinate_slab_intrinsic (by linarith) (by linarith)
  have hDU (i : Bool) : D i ⊆ (U : Set M) := by
    have hpos : 0 < (N i).epsilon⁻¹ := inv_pos.mpr (N i).epsilon_pos
    exact ((N i).coordinate_slab_subset_carrier_m28
      (by linarith) (by linarith)).trans (hNU i)
  have hregion (i : Bool) :
      (N i).region (-((N i).epsilon⁻¹ / 2)) ((N i).epsilon⁻¹ / 2) ⊆ D i := by
    intro x hx
    exact ⟨(N i).coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩,
      (N i).coordinate_map_coordinate_inverse hx.1⟩
  let K := (Middle ∪ D false) ∪ D true
  have hK : IsCompact K := (hMiddle.union (hD false)).union (hD true)
  have hKU : K ⊆ (U : Set M) :=
    union_subset (union_subset hMiddleU (hDU false)) (hDU true)
  have hpK : p ∈ K :=
    Or.inl (Or.inl (hmiddleCapture hpV hpMinus.le hpPlus.le))
  have hqK : q ∈ K :=
    Or.inl (Or.inl (hmiddleCapture hqV hqMinus.le hqPlus.le))
  have hheightK (x : M) (hx : x ∈ K) : lambda ≤ (A.inverse x).2 := by
    rcases hx with (hx | hx) | hx
    · exact hMiddleHeight x hx
    · exact hbackSlab x hx
    · exact hbackHeight x (hUV (hDU true hx)) (hfrontSlab x hx)
  obtain ⟨a0, B0, ha0, _, hB0, hcapture⟩ :=
    A.exists_compactSlab_capturing hK (hKU.trans hUV)
  obtain ⟨B, hmaxB, hB1⟩ := exists_between (max_lt hB0 hlambda.2)
  have hlambdaB : lambda < B := (le_max_right _ _).trans_lt hmaxB
  have hcaptureB : K ⊆ A.compactSlab lambda B := by
    intro x hx
    have hslab := (A.mem_compactSlab_iff ha0 hB0).mp (hcapture hx)
    exact (A.mem_compactSlab_iff hlambda0 hB1).mpr
      ⟨hslab.1, hheightK x hx,
        hslab.2.2.trans ((le_max_left _ _).trans_lt hmaxB).le⟩
  refine ⟨K, B, hK, hKU, hpK, hqK, hheightK, hlambdaB, hB1, hcaptureB, ?_⟩
  intro γ hγ0 hγ1 hγ hγU t ht htK
  have hγV : MapsTo γ (Icc (0 : ℝ) 1) (V : Set M) :=
    fun s hs => hUV (hγU hs)
  have htMiddle : γ t ∉ Middle := fun hx => htK (Or.inl (Or.inl hx))
  have hexitMinus :
      γ t ∉ (N false).region (-((N false).epsilon⁻¹ / 2)) ((N false).epsilon⁻¹ / 2) :=
    fun hx => htK (Or.inl (Or.inr (hregion false hx)))
  have hexitPlus :
      γ t ∉ (N true).region (-((N true).epsilon⁻¹ / 2)) ((N true).epsilon⁻¹ / 2) :=
    fun hx => htK (Or.inr (hregion true hx))
  by_cases htMinus : fMinus (γ t) < 0
  · obtain ⟨c, hc, hcSphere⟩ := exists_sphere_hit_before_positive_height
      hfMinus.neg
      (fun x hx => by simpa only [Pi.neg_apply, neg_eq_zero] using hzeroMinus x hx)
      ht.1 ht.2 hγ hγV
      (by simpa only [Pi.neg_apply, hγ0] using neg_neg_of_pos hpMinus)
      (neg_pos.mpr htMinus)
    obtain ⟨d, hd, hdSphere⟩ := exists_sphere_return_after_negative_height
      hfMinus hzeroMinus ht.1 ht.2 hγ hγV htMinus
      (by simpa only [hγ1] using hqMinus)
    exact ⟨false, c, d, hc.1.le, hc.2.le, hd.1.le, hd.2.le,
      hcSphere, hdSphere, hexitMinus⟩
  · have htPlus : 0 < fPlus (γ t) := by
      by_contra hnot
      exact htMiddle (hmiddleCapture (hγV ht)
        (le_of_not_gt htMinus) (le_of_not_gt hnot))
    obtain ⟨c, hc, hcSphere⟩ := exists_sphere_hit_before_positive_height
      hfPlus hzeroPlus ht.1 ht.2 hγ hγV
      (by simpa only [hγ0] using hpPlus) htPlus
    obtain ⟨d, hd, hdSphere⟩ := exists_sphere_return_after_negative_height
      hfPlus.neg
      (fun x hx => by simpa only [Pi.neg_apply, neg_eq_zero] using hzeroPlus x hx)
      ht.1 ht.2 hγ hγV (neg_neg_of_pos htPlus)
      (by simpa only [Pi.neg_apply, hγ1] using neg_pos.mpr hqPlus)
    exact ⟨true, c, d, hc.1.le, hc.2.le, hd.1.le, hd.2.le,
      hcSphere, hdSphere, hexitPlus⟩

end PoincareConjecture.M28
