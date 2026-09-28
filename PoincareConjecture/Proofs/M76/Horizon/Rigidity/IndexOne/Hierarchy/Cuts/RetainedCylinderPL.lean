import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Cuts.RetainedCylinder
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Bands.StandardPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.OriginalPLInverse

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus.ExactSlabMeridian

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Ann" => squareAnnulus 8 1

variable {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
  {d : β → OpenPartialHomeomorph X V3} {phi : C(H, H)}
  {M : PairedMeridianHierarchy e d phi} {uv : ℝ × ℝ} (m : ExactSlabMeridian M uv)

theorem retainedCylinderParameter_polyhedral_on_interval
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (huv : uv ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ)))
    (l u : ℝ) (hlu : l < u) :
    PolyhedralPLInCharts e m.retainedCylinderParameter (Q ×ˢ Icc l u) := by
  have hphases : ({(uv.1 : C), (uv.2 : C)} : Set C) = {(M.a : C), (M.b : C)} := by
    rcases huv with rfl | rfl
    · rfl
    · simp only [AddCircle.coe_add_period]
      exact pair_comm _ _
  let Auv : ∀ theta ∈ ({(uv.1 : C), (uv.2 : C)} : Set C),
      Ann ≃ₜ sourceSurface M.eta theta := fun theta htheta => M.annuli theta (hphases ▸ htheta)
  let quv : ∀ theta ∈ ({(uv.1 : C), (uv.2 : C)} : Set C), (ℝ × ℝ) → X :=
    fun theta htheta => M.parametrizations theta (hphases ▸ htheta)
  let seam := (uv.1 + uv.2 - p) / 2
  have hca : seam < uv.1 := by dsimp [seam]; linarith [m.short]
  have hvc : uv.2 < seam + p := by dsimp [seam]; linarith [m.short]
  obtain ⟨K, hK, hKS⟩ := exists_finite_hamiltonMeridianBand (a := l) (b := u) hlu
  have hv : FinitePiecewiseAffineOn (standardMeridianBandAffineLift uv.1 uv.2) K.space :=
    (K.affineOnFaces_affine (standardMeridianBandAffineLift uv.1 uv.2)).finitePiecewiseAffineOn hK
  have hqPL : PolyhedralPLInCharts d (standardMeridianBandParameter uv.1 uv.2) K.space :=
    (hd.polyhedralPL_projection hv).congr
      (fun z _ => standardMeridianBandAffineLift_projection uv.1 uv.2 z)
  have hqfront : MapsTo (standardMeridianBandParameter uv.1 uv.2) K.space
      (frontier (sourceSlab (ContinuousMap.id H) uv.1 uv.2)) := fun z hz =>
    mapsTo_standardMeridianBandParameter_frontier uv.1 uv.2 m.ordered m.short
      ⟨(hKS.subset hz).1, mem_univ _⟩
  obtain ⟨g, hg, hgv⟩ := exists_original_frontier_inverse_parameter hd M.eta M.original_pl
    M.identity_homotopy hca m.ordered hvc (M.geometry.frontiers uv huv)
    Auv quv (fun theta htheta => M.parametrizations_pl theta (hphases ▸ htheta))
    (fun theta htheta => M.annuli_exact theta (hphases ▸ htheta))
    m.frontierMap m.fixed_old
    (fun theta htheta x hx => m.annulus_marks theta (hphases ▸ htheta) ⟨x, hx⟩ x.property)
    K hK (standardMeridianBandParameter uv.1 uv.2) hqPL hqfront
  have hgq : PolyhedralPLInCharts e m.retainedCylinderParameter K.space := hg.congr (by
    intro z hz
    rw [hgv z hz, m.retainedCylinderParameter_apply z.1 (hKS.subset hz).1 z.2]
    change (m.frontierMap.symm ⟨standardMeridianBandParameter uv.1 uv.2 z, _⟩ : X) =
      (m.frontierMap.symm (standardSlabBoundaryCoordinates uv.1 uv.2 m.ordered m.short
        (⟨z.1, (hKS.subset hz).1⟩, (z.2 : C))) : X)
    apply congrArg Subtype.val
    apply congrArg m.frontierMap.symm
    apply Subtype.ext
    exact standardMeridianBandParameter_eq_boundary uv.1 uv.2 m.ordered m.short
      ⟨z.1, (hKS.subset hz).1⟩ z.2)
  exact hKS ▸ hgq

theorem retainedCylinderParameter_polyhedral
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (huv : uv ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ))) :
    PolyhedralPLInCharts e m.retainedCylinderParameter
      (Q ×ˢ Icc (m.width / 2) (p - m.width / 2)) :=
  m.retainedCylinderParameter_polyhedral_on_interval hd huv _ _ (by
    norm_num
    linarith [m.width_small])

theorem exists_retainedCylinder_homeomorph
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (huv : uv ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ))) :
    ∃ h : (Q ×ˢ Icc (m.width / 2) (p - m.width / 2)) ≃ₜ
        ↥(frontier (sourceSlab M.eta uv.1 uv.2) \ m.product.openStrip),
      ∀ z, (h z : X) = m.retainedCylinderParameter z := by
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  let S := Q ×ˢ Icc (m.width / 2) (p - m.width / 2)
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    ((isCompact_sphere (0 : V2) 1).prod isCompact_Icc)
  let h : S ≃ₜ m.retainedCylinderParameter '' S :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn m.retainedCylinderParameter S m.retainedCylinderParameter_injective)
      ((m.retainedCylinderParameter_polyhedral hd huv).continuousOn.domRestrict.subtype_mk _)
  exact ⟨h.trans (Homeomorph.setCongr m.retainedCylinderParameter_image), fun _ => rfl⟩

end PoincareConjecture.M76.HamiltonIntervalTorus.ExactSlabMeridian
