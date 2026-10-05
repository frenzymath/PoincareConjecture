import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.MinimizerPowerGrowth
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.Representative
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Morrey.LocalRepresentative

/-!
# Interior continuity of the actual weak annular minimizer

Local cone replacements give uniform contraction, hence power growth of
the actual weak columns. Morrey's representative lies in the closed
observed target and changes neither the weak traces nor the energy.

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
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

/-- Local power growth produces a continuous representative preserving the weak annulus,
energy and minimality. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem M64ObservedWeakAnnulus.continuous_representative
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ W.energy Q) :
    ∃ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
      ContinuousOn W.map S ∧ W.map =ᵐ[mu] A.map ∧ W.column = A.column ∧
      W.energy Q = A.energy Q ∧
      ∀ V : M64ObservedWeakAnnulus (n := n) e c0 c1, W.energy Q ≤ V.energy Q := by
  have hgrowth (a : LoopPlane) (ha : a ∈ S) :=
    A.local_column_power_growth g he hei hread Q hQ hpos hC hcoercive hmin a ha
  obtain ⟨U, hU, hUae⟩ := m64Morrey_local_representative A.observed_memLp
    (fun i => Lp.memLp (A.column i)) A.weak_partial (by
      intro a ha
      obtain ⟨rho, hrho, hsub, K, hK, beta, hbeta, hg⟩ := hgrowth a ha
      exact ⟨rho, hrho, hsub, K, hK, beta, hbeta, fun i b hb r hr => hg b hb r hr i⟩)
  obtain ⟨F, hF, hFae, -⟩ :=
    m64ClosedEmbedding_continuous_representative hei isOpen_interior A.map U hU hUae
  obtain ⟨W, hmap, hcolumn, henergy⟩ := A.with_map_ae F hFae
  refine ⟨W, hmap ▸ hF, hmap ▸ hFae, hcolumn, henergy Q, ?_⟩
  intro V
  rw [henergy]
  exact hmin V

end PoincareMT
