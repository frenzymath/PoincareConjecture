import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BoundedSide
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Leaves
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Matching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Tree











set_option autoImplicit false
open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview


theorem exists_ball_neighborhood
    {Omega : Set (EuclideanSpace Real (Fin 3))}
    (D : Poincare.Manifold.SmoothDomain 3 Omega)
    (f : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 →
      EuclideanSpace Real (Fin 3))
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (hfront : Set.range f = frontier Omega) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace Real (Fin 3))
        (EuclideanSpace Real (Fin 3)),
      Metric.closedBall 0 1 ⊆ e.source ∧
      closure Omega ⊆ e.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      e '' Metric.closedBall 0 1 = closure Omega := by
  obtain ⟨F, hFinj, hFlocal, hFimage⟩ :
      ∃ F : EuclideanSpace Real (Fin 3) → EuclideanSpace Real (Fin 3),
        InjOn F (Metric.closedBall 0 1) ∧
        (∀ x ∈ Metric.closedBall 0 1, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ F x) ∧
        F '' Metric.sphere 0 1 = Set.range f := by
    obtain ⟨M⟩ := nonempty_sphereMorseReduction f hf
    obtain ⟨B, hB⟩ := M.exists_ambient_ball_of_leaf_fillings (by
      intro g hg
      rcases M.exists_filling_or_saddle_core hg with hfill | hcore
      · exact hfill
      obtain ⟨P, hP, hcaps, p, hp, hc, hu, e, he0, hep, he, hei, het, hform⟩ := hcore
      obtain ⟨data, Φ, K, χ, hzero, hΦ, hΦinv, hK, hfix, hχ, hχone, hplanar,
          hlabels, _⟩ := saddle_planar_family_leaf
        M hg P hP hcaps hp hc hu e he0 hep he hei het hform
      let d := data.toTerminalSaddleGeometry
      obtain ⟨_, _, B, hB⟩ :=
        SaddleLevel.exists_global_saddle_matching_of_parametric_interfaces
          (g := d.flatten ∘ g) (d.filledModel.trans d.flatten) Φ hzero hΦ hΦinv
          hfix χ hχ d.I d.A d.B d.C d.modelCaps hχone hplanar
          (by simpa only [d, range_comp, TerminalSaddleGeometry.actualBand]
                using data.actual_decomposition)
          (by simpa only [d, Diffeomorph.coe_trans, image_comp,
              TerminalSaddleGeometry.modelBand] using data.model_decomposition)
          (saddle_cap_replacement_leaf M hg data Φ K χ
            hzero hΦ hΦinv hK hfix hχ hχone hplanar hlabels)
      refine ⟨B.trans d.flatten.symm, ?_⟩
      change (d.flatten.symm ∘ B) '' Metric.sphere 0 1 = _
      rw [image_comp, hB, ← range_comp]
      congr 1
      funext q
      exact d.flatten.symm_apply_apply (g q))
    exact ⟨B, B.injective.injOn, fun x _ => B.isLocalDiffeomorph x, hB⟩
  obtain ⟨e, hs, ht, heq, he, hei⟩ :=
    Poincare.exists_openPartialHomeomorph_of_injOn_compact
      (isCompact_closedBall 0 1) hFinj hFlocal
  have hboundary : e '' Metric.sphere 0 1 = frontier Omega :=
    (Set.image_congr (fun x hx => heq (hs (Metric.sphere_subset_closedBall hx)))).trans
      (hFimage.trans hfront)
  have himage : e '' Metric.closedBall 0 1 = closure Omega :=
    e.image_closedBall_eq_closure_of_boundary
      (by rw [← Module.finrank_eq_rank]; norm_num) hs D.isOpen D.isConnected
      (D.isCompact_closure.isBounded.subset subset_closure) hboundary
  refine ⟨e, hs, ?_, he, hei, himage⟩
  rw [← himage]
  rintro y ⟨x, hx, rfl⟩
  exact e.map_source (hs hx)

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
