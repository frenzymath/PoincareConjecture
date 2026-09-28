import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CylindricalNormalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.TerminalCylinder
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.AmbientTransport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SphereSurgeryCoreCap Poincare.Geometry.Euclidean Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

theorem exists_lower_terminal_cylindrical_preparation
    {v : E3} {g : S2 → E3} {B : Set Real}
    {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (haD : a ≤ D.center) (hDb : D.center < b)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    ∃ r : Real, 0 < r ∧ r < (b - D.center) / 2 ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (G y) = inner Real v y) ∧
        (∃ K : Set E3, IsCompact K ∧
          K ⊆ {y | |inner Real v y - b| ≤ (b - D.center) / 2} ∧
          ∀ y ∉ K, G y = y) ∧
        EqOn G id {y | inner Real v y = b} ∧
        EqOn (G ∘ g) g (D.chart '' closedBall (0 : E2) 1) ∧
        (∀ t ∈ Icc (-r) r, ∀ q : S1,
          G (g (A.chart (q, b + t))) = g (A.chart (q, b)) + t • v) ∧
        ∀ t ∈ Icc (b - r) b,
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (G (g (A.chart (q, t))))) =
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (g (A.chart (q, b)))) := by
  obtain ⟨ε, hε, hsource, hphysical⟩ :=
    A.exists_physical_height_at_terminal (haD.trans hDb.le) hDb.le hgerm
  have hbase (q : S1) : (q, b) ∈ A.chart.source :=
    hsource ⟨mem_univ _, by linarith, by linarith⟩
  have hinj : Injective (fun z : PUnit.{1} × S1 => A.chart (z.2, b)) := by
    intro z z' heq
    exact Prod.ext (Subsingleton.elim _ _)
      (congrArg Prod.fst (A.chart.injOn (hbase z.2) (hbase z'.2) heq))
  obtain ⟨r, hr, hrR, G, hGheight, ⟨K, hK, hKslab, hGfix⟩, hcentral, hmotion⟩ :=
    Saddle.Caps.exists_terminal_cylinder_straightening D.unit_v hg
      (fun _ : PUnit.{1} => A.chart) (fun _ => A.smooth) (fun _ => A.symm_smooth) b
      (fun _ => ⟨ε, hε, hsource, hphysical⟩) hinj
      (half_pos (sub_pos.mpr hDb))
  have hcap : EqOn (G ∘ g) g (D.chart '' closedBall (0 : E2) 1) := by
    intro p hp
    apply hGfix
    intro hmem
    have hs := hKslab hmem
    change |inner Real v (g p) - b| ≤ (b - D.center) / 2 at hs
    have hlow := A.height_le_center_of_mem_cap hp
    have habs := (abs_le.mp hs).1
    linarith
  refine ⟨r, hr, hrR, G, hGheight, ⟨K, hK, hKslab, hGfix⟩, hcentral,
    hcap, hmotion PUnit.unit, ?_⟩
  intro t ht
  have hpoint (q : S1) : G (g (A.chart (q, t))) =
      g (A.chart (q, b)) + (t - b) • v := by
    simpa only [add_sub_cancel] using hmotion PUnit.unit (t - b)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ q
  simp_rw [hpoint, map_add, map_smul]
  simp only [Hemisphere.Plane,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
    smul_zero, add_zero]

theorem exists_prepared_cylindrical_lower_terminal_end_normalization
    {v : E3} {g : S2 → E3} {B : Set Real}
    {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (haD : a ≤ D.center) (hDb : D.center < b)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    ∃ r d u : Real, 0 < r ∧ r < (b - D.center) / 2 ∧
      d < D.center ∧ 0 < u ∧ u < r ∧ d + u < b - u ∧
      ∃ G F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      ∃ Q : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
          (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
        (∀ y, inner Real v (G y) = inner Real v y) ∧
        EqOn G id {y | inner Real v y = b} ∧
        EqOn (G ∘ g) g (D.chart '' closedBall (0 : E2) 1) ∧
        (∀ t ∈ Icc (-r) r, ∀ q : S1,
          G (g (A.chart (q, b + t))) = g (A.chart (q, b)) + t • v) ∧
        (∃ K : Set E3, IsCompact K ∧
          K ⊆ {y | |inner Real v y - b| ≤ (b - D.center) / 2} ∧
          ∀ y ∉ K, G y = y) ∧
        (∃ S : Set E3, IsCompact S ∧ ∀ y ∉ S, F y = y) ∧
        (∀ y, b - u / 4 ≤ inner Real v y → F y = G y) ∧
        (D.planeMap.trans Q.symm) '' sphere (0 : Hemisphere.Plane v) 1 =
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (g (A.chart (q, b)))) ∧
        F '' (g '' A.cappedRegion b) =
          (liftPlaneDiffeomorph D.unit_v d D.scale D.scale_ne_zero
            (D.planeMap.trans Q.symm) '' boundedCylinderNorthernCap v) ∪
          (fun x : Real × Hemisphere.Plane v => x.1 • v + (x.2 : E3)) ''
            (Icc d b ×ˢ range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
              (g (A.chart (q, b))))) := by
  obtain ⟨r, hr, hrR, G, hGheight, ⟨K, hK, hKslab, hGfix⟩, hcentral,
    hcap, hmotion, hcircles⟩ :=
    exists_lower_terminal_cylindrical_preparation A hg haD hDb hgerm
  let g' : S2 → E3 := G ∘ g
  let A' := A.congrEmbedding hcap (fun p => hGheight (g p))
  have hg' : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g' := by
    apply isSmoothEmbedding_of_injective_mfderiv (G.contMDiff.comp hg.contMDiff)
      (G.injective.comp hg.isEmbedding.injective)
    intro p
    rw [mfderiv_comp p (G.contMDiff.mdifferentiable (by simp) _)
      (hg.contMDiff.mdifferentiable (by simp) _)]
    exact (G.mfderivToContinuousLinearEquiv (by simp) (g p)).injective.comp
      (injective_mfderiv_sphere_embedding hg p)
  have hgerm' : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g' q)) := by
    intro p hp
    simpa only [g', Function.comp_apply, hGheight] using hgerm p hp
  have hbase (q : S1) : G (g (A.chart (q, b))) = g (A.chart (q, b)) :=
    hcentral (A.actual_height q b ⟨hDb.le, le_rfl⟩)
  have hconstant : ∀ t ∈ Icc (b - r) b,
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g' (A'.chart (q, t)))) =
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g' (A'.chart (q, b)))) := by
    intro t ht
    change range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
      (G (g (A.chart (q, t))))) = _
    simpa only [g', A', LowerAnnularEnd.congrEmbedding, Function.comp_apply, hbase]
      using hcircles t ht
  obtain ⟨d, u, hdD, hu, hur, hsep, Q, S, hS, R, hQ, hRfix, hRhalf, hend⟩ :=
    exists_supported_cylindrical_lower_terminal_end_normalization A' hg'
      haD hDb hgerm' hr hconstant
  let F := G.trans R
  have hQ' : (D.planeMap.trans Q.symm) '' sphere (0 : Hemisphere.Plane v) 1 =
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
        (g (A.chart (q, b)))) := by
    simpa only [g', A', LowerAnnularEnd.congrEmbedding, congrEmbedding,
      Function.comp_apply, hbase] using hQ
  refine ⟨r, d, u, hr, hrR, hdD, hu, hur, hsep, G, F, Q, hGheight, hcentral,
    hcap, hmotion, ⟨K, hK, hKslab, hGfix⟩, ⟨K ∪ S, hK.union hS, ?_⟩, ?_, hQ', ?_⟩
  · intro y hy
    change R (G y) = y
    rw [hGfix y (fun h => hy (Or.inl h)), hRfix y (fun h => hy (Or.inr h))]
  · intro y hy
    change R (G y) = G y
    exact hRhalf _ (by rw [hGheight]; exact hy)
  · change (R ∘ G) '' (g '' A.cappedRegion b) = _
    simpa only [g', A', LowerAnnularEnd.congrEmbedding, congrEmbedding,
      LowerAnnularEnd.cappedRegion, image_image, Function.comp_apply, hbase] using hend

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
