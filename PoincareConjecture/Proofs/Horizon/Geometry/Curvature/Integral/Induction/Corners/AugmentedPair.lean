import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Tightening
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Submersion









set_option autoImplicit false
open Set
open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace



theorem PoincareConjecture.LeviCivitaData.augmented_strainer_pair_bounds
    {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    (f h : Fin k → M → ℝ) (u v : M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    {S : Set M} {δ H : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / (16 * ((k : ℝ) + 1))) (hH : 0 ≤ H)
    (hunit : ∀ x ∈ S,
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      g.tangentNorm x (D.gradient v x) ≤ 1 ∧
      ∀ i, g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
        g.tangentNorm x (D.gradient (h i) x) ≤ 1)
    (htight : ∀ x ∈ S, ∀ i j, i ≠ j →
      g.inner x (D.gradient (f i) x) (D.gradient (f j) x) ≤ 0)
    (hhess : ∀ x ∈ S, ∀ w : TangentSpace (𝓡 n) x,
      D.hessian u x w w ≤ H * g.inner x w w ∧
      D.hessian v x w w ≤ H * g.inner x w w ∧
      ∀ i, D.hessian (f i) x w w ≤ H * g.inner x w w ∧
        D.hessian (h i) x w w ≤ H * g.inner x w w) :
    let ε := δ / (8 * ((k : ℝ) + 1))
    (∀ x ∈ S,
      g.inner x (D.gradient u x) (D.gradient v x) ≤ -1 + 2 * ε ∧
      ∀ i, g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * ε) →
    (∀ x ∈ S, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ ε ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ ε) →
    (∀ x ∈ S, ∀ i,
      |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤ ε ∧
      |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤ ε ∧
      |g.inner x (D.gradient v x) (D.gradient (f i) x)| ≤ ε ∧
      |g.inner x (D.gradient v x) (D.gradient (h i) x)| ≤ ε) →
    let a := δ / 4
    let β := a / ((k : ℝ) + 1)
    let F := fun x => (1 - a) * u x + β * ∑ i, h i x
    let G := fun x => (1 - a) * v x + β * ∑ i, h i x
    let f' := Fin.cons F f
    let h' := Fin.cons G h
    (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f' i)) ∧
      (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h' i)) ∧
      (∀ x ∈ S,
        (∀ i,
          (1 - 2 * δ ≤ g.tangentNorm x (D.gradient (f' i) x) ∧
            g.tangentNorm x (D.gradient (f' i) x) ≤ 1) ∧
          (1 - 2 * δ ≤ g.tangentNorm x (D.gradient (h' i) x) ∧
            g.tangentNorm x (D.gradient (h' i) x) ≤ 1) ∧
          g.inner x (D.gradient (f' i) x) (D.gradient (h' i) x) ≤ -1 + 2 * δ) ∧
        (∀ i j, i ≠ j →
          |g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x)| ≤ δ ∧
          |g.inner x (D.gradient (h' i) x) (D.gradient (f' j) x)| ≤ δ ∧
          g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x) ≤ 0) ∧
        (∀ i : Fin k,
          g.inner x (D.gradient (f' 0) x) (D.gradient (f' i.succ) x) < 0) ∧
        ∀ w : TangentSpace (𝓡 n) x, ∀ i,
          D.hessian (f' i) x w w ≤ H * g.inner x w w ∧
          D.hessian (h' i) x w w ≤ H * g.inner x w w) ∧
      ∀ x ∈ S, Function.Surjective
        (mfderiv (𝓡 n) 𝓘(ℝ, Fin (k + 1) → ℝ) (fun y i => f' i y) x) := by
  dsimp only
  let ε := δ / (8 * ((k : ℝ) + 1))
  intro hpair holdcross hnewcross
  let a := δ / 4
  let β := a / ((k : ℝ) + 1)
  let F := fun x => (1-a) * u x + β * ∑ i, h i x
  let G := fun x => (1-a) * v x + β * ∑ i, h i x
  let f' : Fin (k+1) → M → ℝ := Fin.cons F f
  let h' : Fin (k+1) → M → ℝ := Fin.cons G h
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hden : 0 < 16 * ((k : ℝ) + 1) := by positivity
  have hmul := (le_div_iff₀ hden).mp hsmall
  have hδ16 : δ ≤ 1/16 := by nlinarith [mul_nonneg hk hδ.le]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεeq : ((k : ℝ)+1)*ε = δ/8 := by dsimp [ε]; field_simp
  have hε8 : ε ≤ δ/8 := by nlinarith [mul_nonneg hk hε]
  have hεδ : ε ≤ δ := by linarith
  have hmix : ε + 2*a ≤ δ := by dsimp [a]; linarith
  have hpairparam : 2*ε+4*a ≤ 2*δ := by dsimp [a]; linarith
  have hmargin : ((Fintype.card (Fin k) : ℝ)+1)*ε < a := by
    simp only [Fintype.card_fin]
    dsimp [a]
    linarith
  obtain ⟨hF, _, hbF⟩ := D.smooth_strainer_extension_tightening f h u v
    hf hh hu hv hε ha ha1 hH hmargin hunit hpair
    (fun x hx i j hij => (holdcross x hx i j hij).2) hnewcross hhess
  have hpair' : ∀ x ∈ S,
      g.inner x (D.gradient v x) (D.gradient u x) ≤ -1+2*ε ∧
      ∀ i, g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1+2*ε := by
    intro x hx
    rw [g.symm x (D.gradient v x) (D.gradient u x)]
    exact hpair x hx
  obtain ⟨hG, _, hbG⟩ := D.smooth_strainer_extension_tightening f h v u
    hf hh hv hu hε ha ha1 hH hmargin
    (fun x hx => ⟨(hunit x hx).2.1,(hunit x hx).1,(hunit x hx).2.2⟩)
    hpair' (fun x hx i j hij => (holdcross x hx i j hij).2)
    (fun x hx i => ⟨(hnewcross x hx i).2.2.1,(hnewcross x hx i).2.2.2,
      (hnewcross x hx i).1,(hnewcross x hx i).2.1⟩)
    (fun x hx w => ⟨(hhess x hx w).2.1,(hhess x hx w).1,(hhess x hx w).2.2⟩)
  simp only [Fintype.card_fin] at hF hG hbF hbG
  have hf' : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f' i) :=
    fun i => Fin.cases hF (fun j => hf j) i
  have hh' : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h' i) :=
    fun i => Fin.cases hG (fun j => hh j) i
  obtain ⟨_, hFgrad, _⟩ := D.strainer_tilt_differential_data u h hu hh a
  obtain ⟨_, hGgrad, _⟩ := D.strainer_tilt_differential_data v h hv hh a
  simp only [Fintype.card_fin] at hFgrad hGgrad
  have hFG (x : M) (hx : x ∈ S) :
      g.inner x (D.gradient F x) (D.gradient G x) ≤ -1+2*δ := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hFn : ‖D.gradient F x‖ ≤ 1 ∧ ‖D.gradient F x-D.gradient u x‖ ≤ 2*a := by
      rw [hFgrad x]
      simpa only [Fintype.card_fin] using
        (Poincare.CurvatureIntegral.strainer_tilt_norm_bounds (D.gradient u x)
          (fun i : Fin k => D.gradient (h i) x) ha ha1
          (hunit x hx).1 (fun i => ((hunit x hx).2.2 i).2))
    have hGn : ‖D.gradient G x‖ ≤ 1 ∧ ‖D.gradient G x-D.gradient v x‖ ≤ 2*a := by
      rw [hGgrad x]
      simpa only [Fintype.card_fin] using
        (Poincare.CurvatureIntegral.strainer_tilt_norm_bounds (D.gradient v x)
          (fun i : Fin k => D.gradient (h i) x) ha ha1
          (hunit x hx).2.1 (fun i => ((hunit x hx).2.2 i).2))
    have h := Poincare.CurvatureIntegral.inner_opposite_le_of_strainer_perturbations
      (D.gradient u x) (D.gradient v x) (D.gradient F x) (D.gradient G x)
      (hunit x hx).1 hGn.1 hFn.2 hGn.2 (hpair x hx).1
    change ⟪D.gradient F x,D.gradient G x⟫_ℝ ≤ -1+2*δ
    linarith
  have hb (x : M) (hx : x ∈ S) :
      (∀ i, g.tangentNorm x (D.gradient (f' i) x) ≤ 1 ∧
        g.tangentNorm x (D.gradient (h' i) x) ≤ 1 ∧
        g.inner x (D.gradient (f' i) x) (D.gradient (h' i) x) ≤ -1+2*δ) ∧
      (∀ i j, i ≠ j →
        |g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x)| ≤ δ ∧
        |g.inner x (D.gradient (h' i) x) (D.gradient (f' j) x)| ≤ δ ∧
        g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x) ≤ 0) ∧
      (∀ i : Fin k,
        g.inner x (D.gradient (f' 0) x) (D.gradient (f' i.succ) x) < 0) ∧
      ∀ w : TangentSpace (𝓡 n) x, ∀ i,
        D.hessian (f' i) x w w ≤ H*g.inner x w w ∧
        D.hessian (h' i) x w w ≤ H*g.inner x w w := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨(hbF x hx).1.2, (hbG x hx).1.2, hFG x hx⟩
      · exact ⟨((hunit x hx).2.2 j).1, ((hunit x hx).2.2 j).2,
          ((hpair x hx).2 j).trans (by linarith)⟩
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · exact fun h => (h rfl).elim
        · intro _
          exact ⟨((hbF x hx).2.2.2.1 j').1.trans hmix,
            ((hbG x hx).2.2.2.1 j').1.trans hmix,
            ((hbF x hx).2.2.2.1 j').2.2.2.2.2.le⟩
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro _
          change |g.inner x (D.gradient (f i') x) (D.gradient F x)| ≤ δ ∧
            |g.inner x (D.gradient (h i') x) (D.gradient F x)| ≤ δ ∧
            g.inner x (D.gradient (f i') x) (D.gradient F x) ≤ 0
          rw [g.symm x (D.gradient (f i') x) (D.gradient F x),
            g.symm x (D.gradient (h i') x) (D.gradient F x)]
          exact ⟨((hbF x hx).2.2.2.1 i').1.trans hmix,
            ((hbF x hx).2.2.2.1 i').2.1.trans hmix,
            ((hbF x hx).2.2.2.1 i').2.2.2.2.2.le⟩
        · intro hij
          have hij' : i' ≠ j' := fun h => hij (congrArg Fin.succ h)
          exact ⟨(holdcross x hx i' j' hij').1.trans hεδ,
            (holdcross x hx i' j' hij').2.trans hεδ, htight x hx i' j' hij'⟩
    · intro i
      exact ((hbF x hx).2.2.2.1 i).2.2.2.2.2
    · intro w i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨((hbF x hx).2.2.2.2 w).1, ((hbG x hx).2.2.2.2 w).1⟩
      · exact (hhess x hx w).2.2 j
  refine ⟨hf', hh', ?_, ?_⟩
  · intro x hx
    obtain ⟨hunit', hcross', htight', hhess'⟩ := hb x hx
    refine ⟨?_, hcross', htight', hhess'⟩
    intro i
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hflo := Poincare.CurvatureIntegral.norm_lower_bound_of_opposite_pair
      (D.gradient (f' i) x) (D.gradient (h' i) x) (hunit' i).2.1 (hunit' i).2.2
    have hhlo := Poincare.CurvatureIntegral.norm_lower_bound_of_opposite_pair
      (D.gradient (h' i) x) (D.gradient (f' i) x) (hunit' i).1
      (by rw [real_inner_comm]; exact (hunit' i).2.2)
    exact ⟨⟨hflo, (hunit' i).1⟩, ⟨hhlo, (hunit' i).2.1⟩, (hunit' i).2.2⟩
  · intro x hx
    have hsmall' : (Fintype.card (Fin (k+1)) : ℝ)*δ < (1-2*δ)^2 := by
      simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
      nlinarith [sq_nonneg (2*δ)]
    have hs := (g.strainer_gradients_regular f' x
      (fun i => D.gradient (h' i) x) hδ.le (by linarith) hsmall'
      (fun i => ((hb x hx).1 i).2.1)
      (fun i => ((hb x hx).1 i).2.2)
      (fun i j hij => ((hb x hx).2.1 i j hij).1)).2
    intro z
    obtain ⟨w, hw⟩ := hs z
    refine ⟨w, ?_⟩
    funext i
    rw [Poincare.Geometry.Manifold.mfderiv_pi_apply f' hf' x w i]
    exact congrFun hw i




theorem PoincareConjecture.LeviCivitaData.augmented_strainer_pair_full_bounds
    {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    (f h : Fin k → M → ℝ) (u v : M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    {S : Set M} {δ H : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / (16 * ((k : ℝ) + 1))) (hH : 0 ≤ H)
    (hunit : ∀ x ∈ S,
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      g.tangentNorm x (D.gradient v x) ≤ 1 ∧
      ∀ i, g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
        g.tangentNorm x (D.gradient (h i) x) ≤ 1)
    (htight : ∀ x ∈ S, ∀ i j, i ≠ j →
      g.inner x (D.gradient (f i) x) (D.gradient (f j) x) ≤ 0)
    (hhess : ∀ x ∈ S, ∀ w : TangentSpace (𝓡 n) x,
      D.hessian u x w w ≤ H * g.inner x w w ∧
      D.hessian v x w w ≤ H * g.inner x w w ∧
      ∀ i, D.hessian (f i) x w w ≤ H * g.inner x w w ∧
        D.hessian (h i) x w w ≤ H * g.inner x w w) :
    let ε := δ / (8 * ((k : ℝ) + 1))
    (∀ x ∈ S,
      g.inner x (D.gradient u x) (D.gradient v x) ≤ -1 + 2 * ε ∧
      ∀ i, g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * ε) →
    (∀ x ∈ S, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ ε ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ ε) →
    (∀ x ∈ S, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (h i) x) (D.gradient (h j) x)| ≤ ε) →
    (∀ x ∈ S, ∀ i,
      |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤ ε ∧
      |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤ ε ∧
      |g.inner x (D.gradient v x) (D.gradient (f i) x)| ≤ ε ∧
      |g.inner x (D.gradient v x) (D.gradient (h i) x)| ≤ ε) →
    let a := δ / 4
    let β := a / ((k : ℝ) + 1)
    let F := fun x => (1 - a) * u x + β * ∑ i, h i x
    let G := fun x => (1 - a) * v x + β * ∑ i, h i x
    let f' := Fin.cons F f
    let h' := Fin.cons G h
    (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f' i)) ∧
      (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h' i)) ∧
      (∀ x ∈ S,
        (∀ i,
          (1 - 2 * δ ≤ g.tangentNorm x (D.gradient (f' i) x) ∧
            g.tangentNorm x (D.gradient (f' i) x) ≤ 1) ∧
          (1 - 2 * δ ≤ g.tangentNorm x (D.gradient (h' i) x) ∧
            g.tangentNorm x (D.gradient (h' i) x) ≤ 1) ∧
          g.inner x (D.gradient (f' i) x) (D.gradient (h' i) x) ≤ -1 + 2 * δ) ∧
        (∀ i j, i ≠ j →
          |g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x)| ≤ δ ∧
          |g.inner x (D.gradient (h' i) x) (D.gradient (f' j) x)| ≤ δ ∧
          |g.inner x (D.gradient (h' i) x) (D.gradient (h' j) x)| ≤ δ ∧
          g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x) ≤ 0) ∧
        (∀ i : Fin k,
          g.inner x (D.gradient (f' 0) x) (D.gradient (f' i.succ) x) < 0) ∧
        ∀ w : TangentSpace (𝓡 n) x, ∀ i,
          D.hessian (f' i) x w w ≤ H * g.inner x w w ∧
          D.hessian (h' i) x w w ≤ H * g.inner x w w) ∧
      ∀ x ∈ S, Function.Surjective
        (mfderiv (𝓡 n) 𝓘(ℝ, Fin (k + 1) → ℝ) (fun y i => f' i y) x) := by
  dsimp only
  let ε := δ / (8 * ((k : ℝ) + 1))
  intro hpair holdcross hnegcross hnewcross
  let a := δ / 4
  let β := a / ((k : ℝ) + 1)
  let F := fun x => (1-a) * u x + β * ∑ i, h i x
  let G := fun x => (1-a) * v x + β * ∑ i, h i x
  let f' : Fin (k+1) → M → ℝ := Fin.cons F f
  let h' : Fin (k+1) → M → ℝ := Fin.cons G h
  obtain ⟨hf', hh', hb, hreg⟩ :=
    D.augmented_strainer_pair_bounds f h u v hf hh hu hv hδ hsmall hH
      hunit htight hhess hpair holdcross hnewcross
  refine ⟨hf', hh', ?_, hreg⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hmul := (le_div_iff₀ (by positivity : 0 < 16*((k : ℝ)+1))).mp hsmall
  have hδ16 : δ ≤ 1/16 := by nlinarith [mul_nonneg hk hδ.le]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεeq : ((k : ℝ)+1)*ε = δ/8 := by dsimp [ε]; field_simp
  have hε8 : ε ≤ δ/8 := by nlinarith [mul_nonneg hk hε]
  have hεδ : ε ≤ δ := by linarith
  have hmix : ε+2*a ≤ δ := by dsimp [a]; linarith
  obtain ⟨_, hGgrad, _⟩ := D.strainer_tilt_differential_data v h hv hh a
  simp only [Fintype.card_fin] at hGgrad
  intro x hx
  obtain ⟨hunit', hcross', htight', hhess'⟩ := hb x hx
  refine ⟨hunit', ?_, htight', hhess'⟩
  have hnew (i : Fin k) :
      |g.inner x (D.gradient G x) (D.gradient (h i) x)| ≤ δ := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hmove : ‖D.gradient G x-D.gradient v x‖ ≤ 2*a := by
      rw [hGgrad x]
      simpa only [Fintype.card_fin] using
        (Poincare.CurvatureIntegral.strainer_tilt_norm_bounds (D.gradient v x)
          (fun i : Fin k => D.gradient (h i) x) ha ha1
          (hunit x hx).2.1 (fun i => ((hunit x hx).2.2 i).2)).2
    exact (Poincare.CurvatureIntegral.abs_inner_le_of_strainer_perturbation
      (D.gradient v x) (D.gradient G x) (D.gradient (h i) x)
      ((hunit x hx).2.2 i).2 hmove (hnewcross x hx i).2.2.2).trans hmix
  intro i j hij
  obtain ⟨hff, hhf, hneg⟩ := hcross' i j hij
  refine ⟨hff, hhf, ?_, hneg⟩
  revert hij
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · exact fun h => (h rfl).elim
    · exact fun _ => hnew j'
  · refine Fin.cases ?_ (fun j' => ?_) j
    · intro _
      change |g.inner x (D.gradient (h i') x) (D.gradient G x)| ≤ δ
      rw [g.symm x (D.gradient (h i') x) (D.gradient G x)]
      exact hnew i'
    · intro hij
      exact (hnegcross x hx i' j' (fun h => hij (congrArg Fin.succ h))).trans hεδ
