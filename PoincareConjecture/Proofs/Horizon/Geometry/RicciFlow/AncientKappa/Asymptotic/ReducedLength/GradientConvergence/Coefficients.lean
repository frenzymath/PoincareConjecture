import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Operations
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactFamily

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.CoordinateMetric

variable {n : ℕ}

abbrev Form (n : ℕ) :=
  EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ

def density (B : Form n) : ℝ :=
  Real.sqrt (Matrix.det (fun i j : Fin n =>
    B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)))

def divergenceMatrix (B : Form n) (i j : Fin n) : ℝ :=
  density B * EuclideanSpace.proj i (B.inverse (EuclideanSpace.proj j))

theorem continuous_density : Continuous (density (n := n)) := by
  unfold density
  apply Real.continuous_sqrt.comp
  apply Continuous.matrix_det
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem continuousOn_divergenceMatrix :
    ContinuousOn (divergenceMatrix (n := n)) {B | B.IsInvertible} := by
  intro B hB
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact continuous_density.continuousAt.mul
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.comp
      ((hB.contDiffAt_map_inverse (n := 0)).continuousAt.clm_apply continuousAt_const))

theorem tendstoUniformlyOn_comp_of_compact
    {X Y Z : Type*} [TopologicalSpace X] [MetricSpace Y] [LocallyCompactSpace Y]
    [UniformSpace Z] {K : Set X} (hK : IsCompact K)
    {U : Set Y} (hU : IsOpen U) {g : X → Y} (hg : ContinuousOn g K)
    (hgU : MapsTo g K U) {gseq : ℕ → X → Y}
    (hconv : TendstoUniformlyOn gseq g atTop K)
    {H : Y → Z} (hH : ContinuousOn H U) :
    TendstoUniformlyOn (fun k x => H (gseq k x)) (fun x => H (g x)) atTop K := by
  obtain ⟨T, hT, hTU, hgseqT⟩ :=
    Poincare.Analysis.Calculus.exists_compact_target_of_tendstoUniformlyOn
      hK hU hg hgU hconv
  have hgT : MapsTo g K T := by
    intro x hx
    exact hT.isClosed.mem_of_tendsto (hconv.tendsto_at hx)
      (hgseqT.mono fun k hk => hk hx)
  exact (hT.uniformContinuousOn_of_continuous (hH.mono hTU)).comp_tendstoUniformlyOn_eventually
    hgseqT hgT hconv

theorem tendstoUniformlyOn_density
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {B : X → Form n} (hB : ContinuousOn B K) {Bseq : ℕ → X → Form n}
    (hconv : TendstoUniformlyOn Bseq B atTop K) :
    TendstoUniformlyOn (fun k x => density (Bseq k x)) (fun x => density (B x))
      atTop K := by
  let := FiniteDimensional.proper ℝ (Form n)
  exact tendstoUniformlyOn_comp_of_compact hK isOpen_univ hB (mapsTo_univ _ _)
    hconv continuous_density.continuousOn

theorem exists_eventually_norm_le_of_compact_limit
    {X Y : Type*} [TopologicalSpace X] [NormedAddCommGroup Y]
    {K : Set X} (hK : IsCompact K) {g : X → Y} (hg : ContinuousOn g K)
    {gseq : ℕ → X → Y} (hconv : TendstoUniformlyOn gseq g atTop K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ‖gseq k x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv 1 (by norm_num)] with k hk x hx
  have hd : ‖gseq k x - g x‖ ≤ 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hk x hx).le
  calc
    ‖gseq k x‖ ≤ ‖gseq k x - g x‖ + ‖g x‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 + C := add_le_add hd (hC x hx)
    _ ≤ max C 0 + 1 := by linarith [le_max_left C 0]

theorem tendstoUniformlyOn_divergenceMatrix
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {B : X → Form n} (hB : ContinuousOn B K)
    (hinv : ∀ x ∈ K, (B x).IsInvertible) {Bseq : ℕ → X → Form n}
    (hconv : TendstoUniformlyOn Bseq B atTop K) :
    TendstoUniformlyOn (fun k x => divergenceMatrix (Bseq k x))
      (fun x => divergenceMatrix (B x)) atTop K := by
  let := FiniteDimensional.proper ℝ (Form n)
  have hU : IsOpen {B : Form n | B.IsInvertible} := ContinuousLinearEquiv.isOpen
  exact tendstoUniformlyOn_comp_of_compact (Y := Form n)
    (U := {B : Form n | B.IsInvertible}) (g := B) hK hU hB
    (fun x hx => hinv x hx) hconv continuousOn_divergenceMatrix

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem density_pullbackCoefficients (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (x : EuclideanSpace ℝ (Fin n)) :
    density (g.pullbackCoefficients e x) = g.pullbackVolumeDensity e x := by
  simp only [density, RiemannianMetric.pullbackVolumeDensity,
    EuclideanSpace.basisFun_apply]
  rfl

theorem divergenceMatrix_pullbackCoefficients (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (x : EuclideanSpace ℝ (Fin n)) :
    divergenceMatrix (g.pullbackCoefficients e x) =
      LeviCivitaData.Dirichlet.divergenceCoefficients g e x := by
  ext i j
  unfold divergenceMatrix LeviCivitaData.Dirichlet.divergenceCoefficients
  rw [density_pullbackCoefficients]

end PoincareConjecture.CoordinateMetric
