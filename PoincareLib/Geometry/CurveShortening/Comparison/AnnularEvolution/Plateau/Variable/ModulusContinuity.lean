import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Variable.ModulusGrowth
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Variable.ModulusMinimizer
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.Representative
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Morrey.LocalRepresentative

/-!
# Actual interior continuity of the weighted annular minimizer

Weighted disk replacement yields genuine column power growth. Morrey
averaging and closed-target lifting construct an interior-continuous
representative preserving all weak traces, columns, and weighted energies.
Applying this to the actual compact-interval minimizer preserves its joint
least property.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareMT

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

/-- Changing only the almost-everywhere representative preserves the literal weighted energy
for every metric and every modulus. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp.
447-449. -/
theorem M64ObservedWeakAnnulus.weightedEnergy_eq_of_map_ae
    (A W : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hmap : W.map =ᵐ[mu] A.map) (hcol : W.column = A.column)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ) :
    W.weightedEnergy Q r = A.weightedEnergy Q r := by
  unfold M64ObservedWeakAnnulus.weightedEnergy
  rw [hcol]
  apply integral_congr_ae
  filter_upwards [hmap] with p hp
  rw [hp]

variable [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]

/-- An actual positive-modulus minimizer has an interior-continuous representative with the
same weak columns and all weighted energies. Proof expansion for Morgan-Tian (2007), Lemma
19.15, pp. 447-449. -/
theorem M64ObservedWeakAnnulus.weighted_continuous_representative
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v) {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ W.weightedEnergy Q modulus) :
    ∃ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
      ContinuousOn W.map S ∧ W.map =ᵐ[mu] A.map ∧ W.column = A.column ∧
      (∀ (B : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ),
        W.weightedEnergy B r = A.weightedEnergy B r) ∧
      ∀ V : M64ObservedWeakAnnulus (n := n) e c0 c1,
        W.weightedEnergy Q modulus ≤ V.weightedEnergy Q modulus := by
  have hgrowth (a : LoopPlane) (ha : a ∈ S) := A.weighted_local_column_power_growth
    g he hei hread Q hQ hpos hC hcoercive hmodulus hmin a ha
  obtain ⟨U, hU, hUae⟩ := m64Morrey_local_representative A.observed_memLp
    (fun i => Lp.memLp (A.column i)) A.weak_partial (by
      intro a ha
      obtain ⟨rho, hrho, hsub, K, hK, beta, hbeta, hg⟩ := hgrowth a ha
      exact ⟨rho, hrho, hsub, K, hK, beta, hbeta, fun i b hb r hr => hg b hb r hr i⟩)
  obtain ⟨F, hF, hFae, -⟩ :=
    m64ClosedEmbedding_continuous_representative hei isOpen_interior A.map U hU hUae
  obtain ⟨W, hmap, hcolumn, -⟩ := A.with_map_ae F hFae
  have hWae : W.map =ᵐ[mu] A.map := hmap ▸ hFae
  have henergy := A.weightedEnergy_eq_of_map_ae W hWae hcolumn
  refine ⟨W, hmap ▸ hF, hWae, hcolumn, henergy, ?_⟩
  intro V
  rw [henergy]
  exact hmin V

/-- The actual joint minimizer on a compact positive modulus interval can be chosen
interior-continuous, with the observed metric constructed from the original intrinsic
geometry. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64ObservedWeakAnnulus_exists_continuous_modulus_minimizer
    (g : RiemannianMetric n M) (e : M → E)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) {c0 c1 : ℝ → M}
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (A0 : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    ∃ (B : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ), r ∈ Icc lo hi ∧
      ∃ L : M64ObservedWeakAnnulus (n := n) e c0 c1,
        Continuous B ∧ (∀ q v, 0 ≤ B q v v) ∧ (∀ q v w, B q v w = B q w v) ∧
        (∀ (f : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 f → ∀ p i j,
          B (f p) (fderiv ℝ (e ∘ f) p (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (fderiv ℝ (e ∘ f) p (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
              m60AreaGram g f p i j) ∧ ContinuousOn L.map S ∧
        ∀ s ∈ Icc lo hi, ∀ A : M64ObservedWeakAnnulus (n := n) e c0 c1,
          L.weightedEnergy B r ≤ A.weightedEnergy B s := by
  obtain ⟨B, r, hr, A, hB, hpos, hsymm, hgram, hmin⟩ :=
    m64ObservedWeakAnnulus_exists_modulus_minimizer g e he hei hread hlo hlohi A0
  obtain ⟨C, hC, hcoercive⟩ := m64ObservedMetric_tangent_coercivity g e he B hgram
  obtain ⟨L, hL, -, -, henergy, -⟩ := A.weighted_continuous_representative
    g he hei hread B hB hpos hC hcoercive (hlo.trans_le hr.1) (hmin r hr)
  refine ⟨B, r, hr, L, hB, hpos, hsymm, hgram, hL, ?_⟩
  intro s hs W
  rw [henergy]
  exact hmin s hs W

end PoincareMT
