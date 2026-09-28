import PoincareConjecture.Proofs.M47.TerminalSourceActualOverlap
import PoincareConjecture.Proofs.M47.TerminalGermsOverlapLimits










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace Poincare.Gluing
open scoped Manifold ContDiff Bundle Topology NNReal

universe u v

namespace PoincareConjecture.M47

open ChartDistance

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ



theorem terminalSourceCountable_source_overlap
    (U : ℕ → Set E) (hU : ∀ n, IsOpen (U n)) [∀ n, Nonempty (Piece U n)]
    {M : ℕ → Type v} [∀ k, MetricSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    (maps : ∀ k n, Piece U n → M k)
    (D : ∀ n n', C(Piece U n × Piece U n', ℝ))
    (hD : ∀ n n' x y, Tendsto (fun k => dist (maps k n x) (maps k n' y)) atTop
      (𝓝 (D n n' (x, y))))
    (L : ℕ → ℝ≥0) (he : ∀ k n, LipschitzWith (L n) (maps k n))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (hlower : ∀ k n x y, c n * dist x y ≤ dist (maps k n x) (maps k n y))
    (hopen : ∀ k n, Topology.IsOpenEmbedding (maps k n))
    (hconn : ∀ k (x : M k) r, IsPreconnected (ball x r))
    (hsmooth : letI : ∀ n, ChartedSpace E (Piece U n) :=
        fun n => (hU n).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k n, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (maps k n))
    (i j : ℕ) (raw : ℕ → SurgeryFlowData.{u}) (origin Q : ℕ → ℝ)
    (C1 C2 : ℕ → GeneralizedSliceCarrier.{u})
    (V1 : ∀ k, Opens (C1 k).carrier) (V2 : ∀ k, Opens (C2 k).carrier)
    {tau1 tau2 s : ℝ} (htau1 : 0 < tau1) (htau2 : 0 < tau2)
    (hs1 : s ∈ Icc (-tau1) 0) (hs2 : s ∈ Icc (-tau2) 0)
    (e1 : ∀ k, SurgeryFlowCylinder (raw k) (C1 k) (origin k) (Q k)
      (Icc (-tau1) 0) (V1 k))
    (e2 : ∀ k, SurgeryFlowCylinder (raw k) (C2 k) (origin k) (Q k)
      (Icc (-tau2) 0) (V2 k))
    (g1 : ∀ k, RiemannianMetric 3 (V1 k)) (g2 : ∀ k, RiemannianMetric 3 (V2 k))
    (hmetric1 : ∀ k (y : V1 k) (a b : TangentSpace (𝓡 3) y),
      (g1 k).inner y a b = (e1 k).pullbackInner s hs1 y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V1 k → (C1 k).carrier) y a)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V1 k → (C1 k).carrier) y b))
    (hmetric2 : ∀ k (y : V2 k) (a b : TangentSpace (𝓡 3) y),
      (g2 k).inner y a b = (e2 k).pullbackInner s hs2 y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V2 k → (C2 k).carrier) y a)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V2 k → (C2 k).carrier) y b))
    (phi1 : ∀ k, E → V1 k) (phi2 : ∀ k, E → V2 k)
    (hphi1 : ∀ k, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (phi1 k) (U i))
    (hphi2 : ∀ k, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (phi2 k) (U j))
    (physical : ∀ k, M k → ((raw k).slice (origin k + 0 / Q k)).carrier)
    (hterminal1 : ∀ k (x : Piece U i), physical k (maps k i x) =
      (e1 k).forward 0 ⟨neg_nonpos.mpr htau1.le, le_rfl⟩ (phi1 k x.val).val)
    (hterminal2 : ∀ k (x : Piece U j), physical k (maps k j x) =
      (e2 k).forward 0 ⟨neg_nonpos.mpr htau2.le, le_rfl⟩ (phi2 k x.val).val)
    (Aseq Bseq : ℕ → E → V)
    (hA : ∀ k, EqOn (Aseq k) ((g1 k).pullbackCoefficients (phi1 k)) (U i))
    (hB : ∀ k, EqOn (Bseq k) ((g2 k).pullbackCoefficients (phi2 k)) (U j)) :
    ∀ x ∈ Subtype.val '' overlap (fun n n' => D n n') i j,
      ∀ᶠ k in atTop, ∀ v w,
        let T := coordinateRepresentative U hU
          (fun y => Function.invFun (maps k j) (maps k i y))
        Bseq k (T x) (fderiv ℝ T x v) (fderiv ℝ T x w) = Aseq k x v w := by
  let : ∀ n, ChartedSpace E (Piece U n) :=
    fun n => (hU n).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ n, IsManifold (𝓡 3) ∞ (Piece U n) :=
    fun n => (hU n).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ n, LocallyCompactSpace (Piece U n) := fun n => (hU n).locallyCompactSpace
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨W, hW, hxW, K, _hK, hrep⟩ :=
    exists_source_transition_neighborhood hD L he c hc hlower hopen hconn hx
  filter_upwards [hrep] with k hk v w
  let T := coordinateRepresentative U hU
    (fun y => Function.invFun (maps k j) (maps k i y))
  have hWcoord : IsOpen (Subtype.val '' W) :=
    (hU i).isOpenEmbedding_subtypeVal.isOpenMap _ hW
  have hWUi : Subtype.val '' W ⊆ U i := by
    rintro _ ⟨y, _, rfl⟩
    exact y.property
  have hT : ContDiffOn ℝ ∞ T (Subtype.val '' W) := by
    apply contDiffOn_coordinateRepresentative
    exact (contMDiffOn_invFun_of_localDiffeomorph (hsmooth k j)
      (hopen k j).injective).comp (hsmooth k i).contMDiff.contMDiffOn
        (fun y hy => image_subset_range _ _ (hk y hy).1)
  have hTU : MapsTo T (Subtype.val '' W) (U j) := by
    rintro _ ⟨y, _hy, rfl⟩
    dsimp only [T]
    rw [coordinateRepresentative_apply]
    exact (Function.invFun (maps k j) (maps k i y)).property
  have hterminal : ∀ y ∈ Subtype.val '' W,
      (e1 k).forward 0 ⟨neg_nonpos.mpr htau1.le, le_rfl⟩ (phi1 k y).val =
        (e2 k).forward 0 ⟨neg_nonpos.mpr htau2.le, le_rfl⟩ (phi2 k (T y)).val := by
    rintro _ ⟨y, hy, rfl⟩
    have hinverse : maps k j (Function.invFun (maps k j) (maps k i y)) = maps k i y :=
      Function.invFun_eq (image_subset_range _ _ (hk y hy).1)
    rw [← hterminal1 k y]
    dsimp only [T]
    rw [coordinateRepresentative_apply, ← hterminal2]
    exact congrArg (physical k) hinverse.symm
  have hI : Icc s 0 ⊆ Icc (-tau1) 0 := fun _ ht => ⟨hs1.1.trans ht.1, ht.2⟩
  have hJ : Icc s 0 ⊆ Icc (-tau2) 0 := fun _ ht => ⟨hs2.1.trans ht.1, ht.2⟩
  have hxcoord : x.val ∈ Subtype.val '' W := mem_image_of_mem _ hxW
  change Bseq k (T x.val) (fderiv ℝ T x.val v) (fderiv ℝ T x.val w) = Aseq k x.val v w
  rw [hB k (hTU hxcoord), hA k x.property]
  exact terminalSource_actual_overlap_coefficients (V1 k) (V2 k) (e1 k) (e2 k)
    hs1.2 hI hJ (g1 k) (g2 k) (hmetric1 k) (hmetric2 k) hWcoord (hU j)
    (phi1 k) (phi2 k) T ((hphi1 k).mono hWUi) (hphi2 k) hT hTU hterminal hxcoord v w

end PoincareConjecture.M47
