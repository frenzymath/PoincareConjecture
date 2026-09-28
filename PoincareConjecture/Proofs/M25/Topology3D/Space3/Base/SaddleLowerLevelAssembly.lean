import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleDiscBoundaries
import PoincareConjecture.Proofs.M25.Topology3D.Space3.PlanarBoundaryDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCircleChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight

set_option autoImplicit false

open Set Function Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_lowerLevelData_of_legs
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (z : ℝ) (hz : z < ⟪(u : E3), psi (D.point, 0)⟫_ℝ)
    (label : Fin 2 → Fin D.capCount)
    (hlabel_injective : Function.Injective label)
    (hlabel_lower : ∀ b, (D.cap (label b)).sign = 1)
    (hseams_lt_level : ∀ i, (D.cap i).sign = 1 →
      (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal < z)
    (leg : Fin 2 → OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere)
    (hleg_source : ∀ b, univ ×ˢ Icc
        ((D.cap (label b)).cutHeight +
          (D.cap (label b)).sign * (D.cap (label b)).removal) z
        ⊆ (leg b).source)
    (hleg_smooth : ∀ b,
      ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞
        (leg b) (leg b).source)
    (hleg_inverse : ∀ b,
      ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
        (leg b).symm (leg b).target)
    (hleg_height : ∀ b p, p ∈ (leg b).source →
      ⟪(u : E3), psi (leg b p, 0)⟫_ℝ = p.2)
    (hleg_bottom : ∀ b, range (fun θ =>
      leg b (θ, (D.cap (label b)).cutHeight +
        (D.cap (label b)).sign * (D.cap (label b)).removal)) =
      (D.cap (label b)).sourceSeam)
    (hleg_disjoint : Disjoint
      ((leg 0) '' (univ ×ˢ Icc
        ((D.cap (label 0)).cutHeight +
          (D.cap (label 0)).sign * (D.cap (label 0)).removal) z))
      ((leg 1) '' (univ ×ˢ Icc
        ((D.cap (label 1)).cutHeight +
          (D.cap (label 1)).sign * (D.cap (label 1)).removal) z)))
    (hleg_cover : (⋃ b, leg b '' (univ ×ˢ Icc
        ((D.cap (label b)).cutHeight +
          (D.cap (label b)).sign * (D.cap (label b)).removal) z)) =
      D.sourceCore ∩ {q | ⟪(u : E3), psi (q, 0)⟫_ℝ ≤ z}) :
    ∃ W : SaddleLowerLevelData D,
      Disjoint (W.disc 0).boundary (W.disc 1).boundary := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let L := heightPlaneCoordinates u
  let c : Fin 2 → UnitCircle → E2 := fun b θ =>
    (L (j (leg b (θ, z)))).1
  have hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j :=
    collar_central_contMDiff psi hpsi
  have hji : Injective j := by
    intro q r hqr
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hqr)
  have htop_source (b : Fin 2) (θ : UnitCircle) :
      (θ, z) ∈ (leg b).source := hleg_source b ⟨mem_univ _,
        (hseams_lt_level (label b) (hlabel_lower b)).le, le_rfl⟩
  have htop_height (b : Fin 2) (θ : UnitCircle) :
      ⟪(u : E3), j (leg b (θ, z))⟫_ℝ = z :=
    hleg_height b _ (htop_source b θ)
  have hc (b : Fin 2) : IsPlanarEmbedding (c b) := by
    obtain ⟨hs, hi, hd⟩ := source_collar_slice_smooth_immersion
      (leg b) (hleg_smooth b) (hleg_inverse b) z (htop_source b)
    let v : UnitCircle → E3 := fun θ => j (leg b (θ, z))
    have hvs : ContMDiff (𝓡 1) 𝓘(ℝ, E3) ∞ v := hj.comp hs
    have hvi : Injective v := hji.comp hi
    have hvd (θ : UnitCircle) :
        Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) v θ) := by
      change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3)
        (j ∘ fun θ => leg b (θ, z)) θ)
      rw [mfderiv_comp θ (hj.mdifferentiable (by simp) _)
        (hs.mdifferentiable (by simp) θ)]
      exact (collar_central_mfderiv_injective psi hpsi _).comp (hd θ)
    exact isPlanarEmbedding_height_projection u v hvs hvi hvd z
      (htop_height b)
  let P : ∀ b : Fin 2, PlanarSchoenfliesData (c b) := fun b =>
    Classical.choice (hP.1 (c b) (hc b))
  let disc : Fin 2 → BallNeighborhoodChart E2 E2 := fun b =>
    (P b).ballNeighborhoodChart
  have hdisc_boundary (b : Fin 2) :
      (fun x : E2 => L.symm (x, z)) '' (disc b).boundary =
        range (fun θ : UnitCircle => psi (leg b (θ, z), 0)) := by
    change (fun x : E2 => L.symm (x, z)) ''
      ((P b).discChart '' Metric.sphere 0 1) = _
    rw [(P b).discChart_image_sphere, ← range_comp]
    have hrec : (fun x : E2 => L.symm (x, z)) ∘ c b =
        (fun θ : UnitCircle => j (leg b (θ, z))) := by
      funext θ
      exact heightPlaneCoordinates_reconstruct u
        (j (leg b (θ, z))) z (htop_height b θ)
    rw [hrec]
  let W : SaddleLowerLevelData D :=
    { level := z
      level_lt_critical := hz
      lower_seams_lt_level := fun i hi => hseams_lt_level i hi
      label := label
      label_injective := hlabel_injective
      label_lower := hlabel_lower
      leg := leg
      leg_source := hleg_source
      leg_smooth := hleg_smooth
      leg_inverse := hleg_inverse
      leg_height := hleg_height
      leg_bottom := hleg_bottom
      leg_disjoint := hleg_disjoint
      leg_cover := hleg_cover
      disc := disc
      disc_boundary := hdisc_boundary }
  exact ⟨W, SaddleLowerLevelData.disc_boundaries_disjoint W hpsi⟩

end PoincareConjecture.M25.Topology3D
