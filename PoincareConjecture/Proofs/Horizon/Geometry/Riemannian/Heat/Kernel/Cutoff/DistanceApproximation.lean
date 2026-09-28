import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.LipschitzApproximation










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators NNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_approx_of_partition_with_error {ι : Type*} [Countable ι]
    (g : RiemannianMetric n M) (r : M → ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓡 n) M)
    (B : ι → ℝ) (hBnonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i x v, |mvfderiv (𝓡 n) (ρ i) x v| ≤ B i * g.tangentNorm x v)
    (hlocal : ∀ i (δ : ℝ), 0 < δ → ∃ f : M → ℝ,
      (∀ x ∈ tsupport (ρ i), ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f x) ∧
      (∀ x ∈ tsupport (ρ i), |f x - r x| ≤ δ) ∧
      (∀ x ∈ tsupport (ρ i), ∀ v,
        |mvfderiv (𝓡 n) f x v| ≤ (3 / 2 : ℝ) * g.tangentNorm x v))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : M → ℝ, ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ u ∧
      (∀ x, |u x - r x| ≤ ε) ∧
      (∀ x v, |mvfderiv (𝓡 n) u x v| ≤ 2 * g.tangentNorm x v) := by
  classical
  let : Encodable ι := Encodable.ofCountable ι
  let δ : ι → ℝ := fun i ↦ min ε ((1 / 2 : ℝ) ^ Encodable.encode i / (4 * (B i + 1)))
  have hδpos : ∀ i, 0 < δ i := by
    intro i
    dsimp [δ]
    exact lt_min hε (div_pos (by positivity) (by have := hBnonneg i; positivity))
  choose f hsmooth herr hgrad using (fun i ↦ hlocal i (δ i) (hδpos i))
  refine ⟨fun x ↦ ∑ᶠ i, ρ i x * f i x, ?_, ?_, ?_⟩
  · simpa only [smul_eq_mul] using ρ.contMDiff_finsum_smul hsmooth
  · intro x
    apply Poincare.abs_partition_mul_sub_le ρ f x (r x) ε
    intro i hi
    exact (herr i x hi).trans (min_le_left _ _)
  · intro x v
    have hN : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
    apply (Poincare.abs_mvfderiv_partition_mul_le ρ f x v (r x) (3 / 2)
      (g.tangentNorm x v)
      (fun i hi ↦ (hsmooth i x hi).mdifferentiableAt (by simp))
      (fun i hi ↦ hgrad i x hi v)).trans
    have heach : ∀ i ∈ ρ.fintsupport x,
        |f i x - r x| * |mvfderiv (𝓡 n) (ρ i) x v| ≤
          ((1 / 2 : ℝ) ^ Encodable.encode i / 4) * g.tangentNorm x v := by
      intro i hi
      have hbudget : δ i * B i ≤ (1 / 2 : ℝ) ^ Encodable.encode i / 4 := by
        have hle := min_le_right ε
          ((1 / 2 : ℝ) ^ Encodable.encode i / (4 * (B i + 1)))
        have hden : 0 < 4 * (B i + 1) := by have := hBnonneg i; positivity
        have hmul := (le_div_iff₀ hden).mp hle
        change δ i * (4 * (B i + 1)) ≤ (1 / 2 : ℝ) ^ Encodable.encode i at hmul
        have := hδpos i
        nlinarith
      calc
        |f i x - r x| * |mvfderiv (𝓡 n) (ρ i) x v|
          ≤ δ i * (B i * g.tangentNorm x v) :=
            mul_le_mul (herr i x ((ρ.mem_fintsupport_iff x i).mp hi)) (hB i x v)
              (abs_nonneg _) (hδpos i).le
        _ ≤ ((1 / 2 : ℝ) ^ Encodable.encode i / 4) * g.tangentNorm x v := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right hbudget hN
    have hsum := Finset.sum_le_sum heach
    rw [← Finset.sum_mul, ← Finset.sum_div] at hsum
    have hgeom : ∑ i ∈ ρ.fintsupport x, (1 / (2 : ℝ)) ^ Encodable.encode i ≤ 2 := by
      have h := (summable_geometric_two.sum_le_tsum
        ((ρ.fintsupport x).map ⟨Encodable.encode, Encodable.encode_injective⟩)
        (fun _ _ ↦ by positivity)).trans_eq tsum_geometric_two
      simpa only [Finset.sum_map, Function.Embedding.coeFn_mk] using h
    have htotal := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hgeom (by norm_num : (0 : ℝ) ≤ 4)) hN
    nlinarith



theorem exists_approx_of_local_with_error [T2Space M] [SigmaCompactSpace M]
    (g : RiemannianMetric n M) (r : M → ℝ)
    (hlocal : ∀ p : M, ∃ U : Set M, U ∈ 𝓝 p ∧ ∀ δ : ℝ, 0 < δ → ∃ f : M → ℝ,
      (∀ x ∈ U, ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f x) ∧
      (∀ x ∈ U, |f x - r x| ≤ δ) ∧
      (∀ x ∈ U, ∀ v,
        |mvfderiv (𝓡 n) f x v| ≤ (3 / 2 : ℝ) * g.tangentNorm x v))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : M → ℝ, ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ u ∧
      (∀ x, |u x - r x| ≤ ε) ∧
      (∀ x v, |mvfderiv (𝓡 n) u x v| ≤ 2 * g.tangentNorm x v) := by
  classical
  choose U hU hf using hlocal
  obtain ⟨ι, fs, hfs⟩ := SmoothBumpCovering.exists_isSubordinate (𝓡 n)
    isClosed_univ (fun p _ ↦ hU p)
  let : Encodable ι := fs.locallyFinite.encodable (fun i ↦ (fs i).nonempty_support)
  let ρ := fs.toSmoothPartitionOfUnity
  have hc (i : ι) : HasCompactSupport (ρ i) :=
    (fs i).hasCompactSupport.mono (fs.support_toSmoothPartitionOfUnity_subset i)
  choose B hB hBd using fun i ↦
    g.exists_metric_derivative_bound_of_hasCompactSupport (ρ i).contMDiff (hc i)
  apply g.exists_approx_of_partition_with_error r ρ B hB hBd ?_ hε
  intro i δ hδ
  obtain ⟨f, hsm, he, hd⟩ := hf (fs.c i) δ hδ
  have hs : tsupport (ρ i) ⊆ U (fs.c i) := hfs.toSmoothPartitionOfUnity i
  exact ⟨f, fun x hx ↦ hsm x (hs hx), fun x hx ↦ he x (hs hx),
    fun x hx ↦ hd x (hs hx)⟩



theorem exists_smooth_distance_approx_with_error [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric n M) (O : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : M → ℝ, ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ u ∧
      (∀ x, |u x - (g.edist O x).toReal| ≤ ε) ∧
      (∀ x v, |mvfderiv (𝓡 n) u x v| ≤ 2 * g.tangentNorm x v) := by
  let : SecondCountableTopology M := g.secondCountableTopology
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  exact g.exists_approx_of_local_with_error _ (g.exists_local_distance_approx O) hε

end PoincareConjecture.RiemannianMetric
