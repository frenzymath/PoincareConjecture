import PoincareConjecture.Proofs.M47.CanonicalScalarStability
import PoincareConjecture.Proofs.M47.ComponentEstimateGeometry
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.SectionalParameters
import PoincareConjecture.Proofs.M44.Mathlib.SectionalNormalization
import PoincareConjecture.Proofs.M13.CurvatureMultilinear
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M04

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M]

theorem sectional_lower_on_independent_pair {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (x : M) (A : ℝ)
    (hA : ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x v w → A < D.sectionalCurvature x v w)
    (u v : TangentSpace (𝓡 3) x) (hlin : LinearIndependent ℝ ![u, v]) :
    A < D.sectionalCurvature x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨p, q, hp, hq, hpq, hvalue⟩ :=
    M44.exists_orthonormal_curvature_quotient (M13.curvatureTensorLinear D x)
      (fun a b c d => D.curvatureTensor_swap_first x a b c d)
      (fun a b c d => D.curvatureTensor_swap_last x a b c d) u v
      (metricGram_pos_of_linearIndependent g x u v hlin)
  change g.inner x p p = 1 at hp
  change g.inner x q q = 1 at hq
  change g.inner x p q = 0 at hpq
  change D.curvatureTensor x p q p q = D.sectionalCurvature x u v at hvalue
  have h := hA p q ⟨hp, hq, hpq⟩
  simpa only [LeviCivitaData.sectionalCurvature, hp, hq, hpq, one_mul,
    zero_pow (by decide : 2 ≠ 0), sub_zero, div_one, hvalue] using h

theorem exists_sectional_lower_near_time_on_compact [CompactSpace M]
    {J : Set ℝ} (F : RicciFlow 3 M J) (t : J) {K : Set M} (hK : IsCompact K)
    (A : ℝ) (hA : ∀ x ∈ K, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric t.val) x v w →
        A < (F.connection t.val).sectionalCurvature x v w) :
    ∃ m : ℝ, A < m ∧ ∀ᶠ s : J in 𝓝 t, ∀ x ∈ K,
      ∀ v w : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (F.metric s.val) x v w →
          m ≤ (F.connection s.val).sectionalCurvature x v w := by
  obtain ⟨P⟩ := M46.compactSectionalParameters F
  let Z : Set P.carrier := P.point ⁻¹' K
  have hZ : IsCompact Z := (hK.isClosed.preimage P.point_continuous).isCompact
  let q : J → P.carrier → ℝ := fun s z =>
    (F.connection s.val).curvatureTensor (P.point z) (P.left z) (P.right z)
      (P.left z) (P.right z) /
      metricGram (F.metric s.val) (P.point z) (P.left z) (P.right z)
  have hq : Continuous (Function.uncurry q) := by
    have hmap : Continuous (fun p : J × P.carrier => (p.1.val, p.2)) := by fun_prop
    have h := P.continuous_quotient.comp_continuous hmap
      (fun p => ⟨p.1.property, mem_univ p.2⟩)
    exact h
  have hqt : Continuous (q t) := hq.comp (continuous_const.prodMk continuous_id)
  have hstrict (z : P.carrier) (hz : z ∈ Z) : A < q t z := by
    simpa only [q, LeviCivitaData.sectionalCurvature, metricGram] using
      sectional_lower_on_independent_pair (F.connection t.val) (P.point z) A
        (hA (P.point z) hz) (P.left z) (P.right z) (P.independent z)
  obtain ⟨q0, hq0, hlower⟩ := hZ.exists_forall_le' hqt.continuousOn hstrict
  let m := (A + q0) / 2
  have hm : A < m := by dsimp only [m]; linarith
  have hmin (z : P.carrier) (hz : z ∈ Z) : m < q t z := by
    dsimp only [m]
    linarith [hlower z hz]
  have hnear : ∀ᶠ s : J in 𝓝 t, ∀ z ∈ Z, m < q s z := by
    apply hZ.eventually_forall_of_forall_eventually
    intro z hz
    exact hq.continuousAt.eventually (Ioi_mem_nhds (hmin z hz))
  refine ⟨m, hm, ?_⟩
  filter_upwards [hnear] with s hs
  have hfull := P.complete_on K s.val m (fun z hz =>
    (le_div_iff₀ (metricGram_pos_of_linearIndependent (F.metric s.val)
      (P.point z) (P.left z) (P.right z) (P.independent z))).mp (hs z hz).le)
  intro x hx v w hpair
  have h := hfull x hx v w
  simpa only [LeviCivitaData.sectionalCurvature, metricGram, hpair.1, hpair.2.1,
    hpair.2.2, one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one, mul_one] using h

theorem component_sectional_bounds_persist [CompactSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow 3 M J) (t : J)
    {C : ℝ} (N : SingularCComponent (F.metric t.val) (F.connection t.val) C) :
    ∀ᶠ s : J in 𝓝 t,
      (∀ x ∈ N.carrier, ∀ v w : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (F.metric s.val) x v w →
          0 < (F.connection s.val).sectionalCurvature x v w) ∧
      ∀ x ∈ N.carrier, ∀ v w : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (F.metric s.val) x v w →
          C⁻¹ * scalarCurvatureSupOn (F.metric s.val) (F.connection s.val) N.carrier <
            (F.connection s.val).sectionalCurvature x v w := by
  have hbase : N.basepoint ∈ N.carrier := by
    rw [N.component_eq]
    exact mem_connectedComponent
  have hsup : 0 < scalarCurvatureSupOn (F.metric t.val) (F.connection t.val) N.carrier :=
    (PoincareConjecture.M47.component_scalar_pos N hbase).trans_le
      (PoincareConjecture.M47.component_scalar_le_sup N hbase)
  let A := C⁻¹ * scalarCurvatureSupOn (F.metric t.val) (F.connection t.val) N.carrier
  have hA : 0 < A := mul_pos (inv_pos.mpr N.constant_pos) hsup
  obtain ⟨m, hm, hnear⟩ := exists_sectional_lower_near_time_on_compact
    F t N.compact A N.sectional_lower
  have hscalar : Continuous (fun s : J =>
      C⁻¹ * scalarCurvatureSupOn (F.metric s.val) (F.connection s.val) N.carrier) :=
    continuous_const.mul (continuous_scalarSup_on_compact hC F N.compact)
  have hmargin := hscalar.continuousAt.eventually_lt continuousAt_const hm
  filter_upwards [hnear, hmargin] with s hs hthreshold
  exact ⟨fun x hx v w hp => (hA.trans hm).trans_le (hs x hx v w hp),
    fun x hx v w hp => hthreshold.trans_le (hs x hx v w hp)⟩

end PoincareConjecture.Proofs.M47
