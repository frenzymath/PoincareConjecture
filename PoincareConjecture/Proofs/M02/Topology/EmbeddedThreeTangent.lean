import PoincareConjecture.Proofs.M02.Topology.UniformLocalThreeGraphs
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {N : Nat} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

def embeddedThreeTangent (e : C(M, EuclideanSpace Real (Fin N))) (p : M) :
    Submodule Real (EuclideanSpace Real (Fin N)) :=
  (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e p).range

theorem embeddedThreeTangent_finrank
    {N : Nat} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (e : C(M, EuclideanSpace Real (Fin N)))
    (p : M) (hi : Function.Injective
      (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e p)) :
    Module.finrank Real (embeddedThreeTangent e p) = 3 := by
  let L := mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e p
  calc
    Module.finrank Real (embeddedThreeTangent e p) =
        Module.finrank Real (EuclideanSpace Real (Fin 3)) :=
      (LinearEquiv.ofInjective L.toLinearMap hi).finrank_eq.symm
    _ = 3 := finrank_euclideanSpace_fin

set_option maxHeartbeats 2000000 in

theorem exists_uniform_embedded_three_graph [T2Space M] [CompactSpace M] [Nonempty M]
    (e : C(M, EuclideanSpace Real (Fin N)))
    (hs : ContMDiff (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) ∞ e)
    (he : _root_.Topology.IsClosedEmbedding e)
    (hi : ∀ p : M, Function.Injective
      (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e p))
    (epsilon : NNReal) (hepsilon : 0 < epsilon) :
    ∃ rho : Real, 0 < rho ∧ ∀ p : M,
      ∃ g : OpenPartialHomeomorph (embeddedThreeTangent e p) M,
        g.source = Metric.ball 0 (2 * rho) ∧
        g 0 = p ∧
        (∀ v ∈ g.source,
          (embeddedThreeTangent e p).orthogonalProjectionOnto (e (g v) - e p) = v) ∧
        LipschitzOnWith epsilon
          (fun v : embeddedThreeTangent e p =>
            e (g v) - e p - (v : EuclideanSpace Real (Fin N))) g.source ∧
        (∀ q : M, dist (e q) (e p) < rho → q ∈ g.target) := by
  classical
  have hlocal : ∀ p0 : M, ∃ U : Set M, IsOpen U ∧ p0 ∈ U ∧
      ∃ r d : Real, 0 < r ∧ 0 < d ∧ ∀ p ∈ U,
        ∃ g : OpenPartialHomeomorph (embeddedThreeTangent e p) M,
          g.source = Metric.ball 0 (2 * r) ∧ g 0 = p ∧
          (∀ v ∈ g.source,
            (embeddedThreeTangent e p).orthogonalProjectionOnto (e (g v) - e p) = v) ∧
          LipschitzOnWith epsilon
            (fun v : embeddedThreeTangent e p =>
              e (g v) - e p - (v : EuclideanSpace Real (Fin N))) g.source ∧
          (∀ q : M, dist (e q) (e p) < d → q ∈ g.target) := by
    intro p0
    let c := chartAt (EuclideanSpace Real (Fin 3)) p0
    let F : EuclideanSpace Real (Fin 3) → EuclideanSpace Real (Fin N) := e ∘ c.symm
    have hp0 : p0 ∈ c.source := mem_chart_source _ _
    have hx0 : c p0 ∈ c.target := c.map_source hp0
    have hF : ContDiffOn Real ∞ F c.target :=
      (hs.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓡 3) (x := p0))).contDiffOn
    have hc : c.MDifferentiable (𝓡 3) (𝓡 3) := mdifferentiable_chart p0
    have hderiv (x : EuclideanSpace Real (Fin 3)) (hx : x ∈ c.target) :
        fderiv Real F x =
          (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e (c.symm x)).comp
            (mfderiv (𝓡 3) (𝓡 3) c.symm x) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp x ((hs.mdifferentiable (by simp)).mdifferentiableAt)
        (hc.symm.mdifferentiableAt hx)
    have hFi : Function.Injective (fderiv Real F (c p0)) := by
      rw [hderiv _ hx0]
      exact (hi (c.symm (c p0))).comp (hc.symm.mfderiv_injective hx0)
    obtain ⟨R, r, hR, hr, hball, hgraphs⟩ :=
      exists_uniform_local_three_graphs F c.target c.open_target hF (c p0) hx0 hFi
        epsilon hepsilon
    let U := c.source ∩ c ⁻¹' Metric.ball (c p0) (R / 2)
    let V := c.source ∩ c ⁻¹' Metric.ball (c p0) R
    let K := c.symm '' Metric.closedBall (c p0) (R / 2)
    have hU : IsOpen U := c.isOpen_inter_preimage Metric.isOpen_ball
    have hV : IsOpen V := c.isOpen_inter_preimage Metric.isOpen_ball
    have hcb : Metric.closedBall (c p0) (R / 2) ⊆ c.target := by
      intro x hx
      apply hball
      exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith))
    have hK : IsCompact K :=
      (isCompact_closedBall (c p0) (R / 2)).image_of_continuousOn
        (c.symm.continuousOn.mono hcb)
    have hKV : K ⊆ V := by
      rintro p ⟨x, hx, rfl⟩
      refine ⟨c.symm.map_source (hcb hx), ?_⟩
      change dist (c (c.symm x)) (c p0) < R
      rw [c.right_inv (hcb hx)]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)
    have hUK : U ⊆ K := by
      intro p hp
      exact ⟨c p, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hp.2)),
        c.left_inv hp.1⟩
    have hsep : Disjoint (e '' K) (e '' Vᶜ) := by
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
      have hqp : q = p := he.injective heq
      exact hq (hqp ▸ hKV hp)
    obtain ⟨delta, hdelta, hdist⟩ := Metric.exists_pos_forall_lt_edist
      (hK.image e.continuous) ((isClosed_compl_iff.mpr hV).isCompact.image e.continuous).isClosed
      hsep
    have hdeltaR : 0 < (delta : Real) := hdelta
    refine ⟨U, hU, ⟨hp0, by simpa using half_pos hR⟩,
      r, min r (delta : Real), hr, lt_min hr hdeltaR, ?_⟩
    intro p hp
    have hpc : c p ∈ Metric.ball (c p0) R :=
      Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hp.2) (by linarith))
    have hcp : c p ∈ c.target := c.map_source hp.1
    have hT : (fderiv Real F (c p)).range = embeddedThreeTangent e p := by
      rw [hderiv _ hcp]
      change LinearMap.range
        ((mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e (c.symm (c p))).toLinearMap.comp
          (mfderiv (𝓡 3) (𝓡 3) c.symm (c p)).toLinearMap) = _
      rw [LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.mpr (hc.symm.mfderiv_surjective hcp))]
      rw [c.left_inv hp.1]
      rfl
    obtain ⟨g0, hg0s, hg00, hg0t, hg0proj, hg0lip, hg0cover⟩ := hgraphs (c p) hpc
    have hFp : F (c p) = e p := congrArg e (c.left_inv hp.1)
    have hconverted : ∃ g : OpenPartialHomeomorph (embeddedThreeTangent e p)
          (EuclideanSpace Real (Fin 3)),
        g.source = Metric.ball 0 (2 * r) ∧ g 0 = c p ∧
        g.target ⊆ Metric.ball (c p0) (4 * R) ∧
        (∀ v ∈ g.source, (embeddedThreeTangent e p).orthogonalProjectionOnto
          (e (c.symm (g v)) - e p) = v) ∧
        LipschitzOnWith epsilon (fun v : embeddedThreeTangent e p =>
          e (c.symm (g v)) - e p - (v : EuclideanSpace Real (Fin N))) g.source ∧
        (∀ q ∈ Metric.ball (c p0) R, dist (F q) (e p) < r → q ∈ g.target) := by
      rw [← hT]
      refine ⟨g0, hg0s, hg00, hg0t, ?_, ?_, ?_⟩
      · simpa only [F, Function.comp_apply, c.left_inv hp.1] using hg0proj
      · simpa only [F, Function.comp_apply, c.left_inv hp.1] using hg0lip
      · simpa only [hFp] using hg0cover
    obtain ⟨g, hgs, hg0, hgt, hgproj, hglip, hgcover⟩ := hconverted
    let G := g.trans c.symm
    have hGs : G.source = g.source := by
      change g.source ∩ g ⁻¹' c.target = g.source
      exact Set.inter_eq_left.mpr (fun v hv => hball (hgt (g.map_source hv)))
    refine ⟨G, hGs.trans hgs, ?_, ?_, ?_, ?_⟩
    · change c.symm (g 0) = p
      rw [hg0, c.left_inv hp.1]
    · rw [hGs]
      simpa only [G, OpenPartialHomeomorph.coe_trans, Function.comp_apply] using hgproj
    · rw [hGs]
      simpa only [G, OpenPartialHomeomorph.coe_trans, Function.comp_apply] using hglip
    · intro q hq
      have hqV : q ∈ V := by
        by_contra hnq
        have hh := hdist (e p) ⟨p, hUK hp, rfl⟩ (e q) ⟨q, hnq, rfl⟩
        have hhR : (delta : Real) < dist (e p) (e q) := by
          simpa only [edist_dist, ← ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg delta.coe_nonneg] using hh
        rw [dist_comm] at hhR
        exact (not_lt_of_ge (le_of_lt (lt_of_lt_of_le hq (min_le_right _ _)))) hhR
      change q ∈ c.source ∩ c ⁻¹' g.target
      refine ⟨hqV.1, hgcover (c q) hqV.2 ?_⟩
      have hFq : F (c q) = e q := congrArg e (c.left_inv hqV.1)
      rw [hFq]
      exact lt_of_lt_of_le hq (min_le_left _ _)
  choose U hUo hUc r d hr hd hG using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun p _ => Set.mem_iUnion.mpr ⟨p, hUc p⟩)
  have hbound : ∃ rho : Real, 0 < rho ∧ ∀ i ∈ t, rho ≤ min (r i) (d i) := by
    clear ht
    induction t using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i t hi ih =>
        obtain ⟨rho, hpos, hb⟩ := ih
        refine ⟨min rho (min (r i) (d i)), lt_min hpos (lt_min (hr i) (hd i)), ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hb j hj)
  obtain ⟨rho, hrho, hbound⟩ := hbound
  refine ⟨rho, hrho, ?_⟩
  intro p
  obtain ⟨i, hi, hp⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
  obtain ⟨g, hgs, hg0, hgproj, hglip, hgcover⟩ := hG i p hp
  have hrhoi : rho ≤ r i := (hbound i hi).trans (min_le_left _ _)
  have hrhod : rho ≤ d i := (hbound i hi).trans (min_le_right _ _)
  let G := g.restrOpen (Metric.ball 0 (2 * rho)) Metric.isOpen_ball
  have hGs : G.source = Metric.ball 0 (2 * rho) := by
    rw [OpenPartialHomeomorph.restrOpen_source, hgs]
    exact Set.inter_eq_right.mpr (Metric.ball_subset_ball (by linarith))
  refine ⟨G, hGs, hg0, ?_, ?_, ?_⟩
  · intro v hv
    exact hgproj v hv.1
  · exact hglip.mono Set.inter_subset_left
  · intro q hq
    have hqt : q ∈ g.target := hgcover q (lt_of_lt_of_le hq hrhod)
    change q ∈ g.target ∩ g.symm ⁻¹' Metric.ball 0 (2 * rho)
    refine ⟨hqt, ?_⟩
    have hcoord := hgproj (g.symm q) (g.map_target hqt)
    rw [g.right_inv hqt] at hcoord
    have hn : ‖g.symm q‖ ≤ dist (e q) (e p) := by
      rw [← hcoord, dist_eq_norm]
      exact (embeddedThreeTangent e p).norm_orthogonalProjectionOnto_apply_le _
    change dist (g.symm q) 0 < 2 * rho
    rw [dist_zero_right]
    exact lt_of_le_of_lt hn (lt_trans hq (by linarith))

end PoincareConjecture.Proofs.M02.Topology
