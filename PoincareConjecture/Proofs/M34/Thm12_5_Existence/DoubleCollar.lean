import PoincareConjecture.Proofs.M34.Thm12_5_Existence.EndReflection
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.EndTruncation











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}



def endDoubleCollar (e : StandardCylindricalEnd g) (L : ℝ) : Set StandardCapSpace :=
  e.coordinate '' (univ ×ˢ Ioo (L - 1) (L + 1))



theorem endDoubleCollar_isOpen (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : IsOpen (endDoubleCollar e L) := by
  apply end_isOpen_coordinate_image e (isOpen_univ.prod isOpen_Ioo)
  intro z hz
  have hh := hz.2.1
  linarith



theorem endDoubleCollar_subset_truncation (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : endDoubleCollar e L ⊆ endTruncation e (L + 1) := by
  rintro _ ⟨z, hz, rfl⟩
  have hzpos : 0 ≤ z.2 := by linarith [hz.2.1]
  exact (endTruncation_coordinate_iff e (by linarith) hzpos).mpr hz.2.2



theorem endAxialReflection_maps_collar (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    MapsTo (endAxialReflection e (2 * L)) (endDoubleCollar e L) (endDoubleCollar e L) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [endAxialReflection_coordinate e (2 * L) (by linarith [hz.2.1])]
  refine ⟨(z.1, 2 * L - z.2), ⟨mem_univ _, ?_, ?_⟩, rfl⟩ <;>
    dsimp only <;> linarith [hz.2.1, hz.2.2]



theorem endAxialReflection_collar_leftInvOn (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    LeftInvOn (endAxialReflection e (2 * L)) (endAxialReflection e (2 * L))
      (endDoubleCollar e L) := by
  rintro _ ⟨z, hz, rfl⟩
  exact endAxialReflection_involutive e (2 * L)
    (by linarith [hz.2.1]) (by linarith [hz.2.2])



theorem endAxialReflection_collar_contMDiffOn (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (endAxialReflection e (2 * L)) (endDoubleCollar e L) := by
  rintro _ ⟨z, hz, rfl⟩
  exact (endAxialReflection_contMDiffAt e (2 * L)
    (by linarith [hz.2.1]) (by linarith [hz.2.2])).contMDiffWithinAt



def endDoubleCollarHomeomorph (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : OpenPartialHomeomorph StandardCapSpace StandardCapSpace where
  toFun := endAxialReflection e (2 * L)
  invFun := endAxialReflection e (2 * L)
  source := endDoubleCollar e L
  target := endDoubleCollar e L
  map_source' := endAxialReflection_maps_collar e hL
  map_target' := endAxialReflection_maps_collar e hL
  left_inv' := endAxialReflection_collar_leftInvOn e hL
  right_inv' := endAxialReflection_collar_leftInvOn e hL
  open_source := endDoubleCollar_isOpen e hL
  open_target := endDoubleCollar_isOpen e hL
  continuousOn_toFun := (endAxialReflection_collar_contMDiffOn e hL).continuousOn
  continuousOn_invFun := (endAxialReflection_collar_contMDiffOn e hL).continuousOn



theorem endDoubleCollarHomeomorph_symm (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : (endDoubleCollarHomeomorph e hL).symm =
      endDoubleCollarHomeomorph e hL := rfl



def endClosedReflectionGraph (e : StandardCylindricalEnd g) (L : ℝ) :
    Set (StandardCapSpace × StandardCapSpace) :=
  (fun z : StandardCylinderSpace =>
    (e.coordinate z, e.coordinate (cylinderAxialReflection (2 * L) z))) ''
      (univ ×ˢ Icc (L - 1) (L + 1))



theorem endClosedReflectionGraph_isCompact (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : IsCompact (endClosedReflectionGraph e L) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply ContinuousOn.prodMk
  · apply e.coordinate_smooth.continuousOn.mono
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    change -e.collar < z.2
    linarith [hz.2.1, e.collar_pos]
  · apply e.coordinate_smooth.continuousOn.comp
      (cylinderAxialReflection_contMDiff (2 * L)).continuous.continuousOn
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    change -e.collar < 2 * L - z.2
    linarith [hz.2.2, e.collar_pos]



theorem endClosedReflectionGraph_iff (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) {x y : StandardCapSpace}
    (hx : x ∈ endTruncation e (L + 1)) (hy : y ∈ endTruncation e (L + 1)) :
    (x, y) ∈ endClosedReflectionGraph e L ↔
      x ∈ endDoubleCollar e L ∧ endAxialReflection e (2 * L) x = y := by
  constructor
  · rintro ⟨z, hz, heq⟩
    have hxz : e.coordinate z = x := congrArg Prod.fst heq
    have hyz : e.coordinate (z.1, 2 * L - z.2) = y := congrArg Prod.snd heq
    have hzpos : 0 ≤ z.2 := by linarith [hz.2.1]
    have hzref : 0 ≤ 2 * L - z.2 := by linarith [hz.2.2]
    have hupper : z.2 < L + 1 := (endTruncation_coordinate_iff e (by linarith) hzpos).mp
      (by rw [hxz]; exact hx)
    have hlower' : 2 * L - z.2 < L + 1 :=
      (endTruncation_coordinate_iff e (L := L + 1) (by linarith)
        (z := (z.1, 2 * L - z.2)) hzref).mp (by rw [hyz]; exact hy)
    refine ⟨⟨z, ⟨mem_univ _, by linarith, hupper⟩, hxz⟩, ?_⟩
    rw [← hxz, endAxialReflection_coordinate e (2 * L) hzpos]
    exact hyz
  · rintro ⟨⟨z, hz, rfl⟩, hyz⟩
    have hzpos : 0 ≤ z.2 := by linarith [hz.2.1]
    refine ⟨z, ⟨mem_univ _, hz.2.1.le, hz.2.2.le⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact (endAxialReflection_coordinate e (2 * L) hzpos).symm.trans hyz

end PoincareConjecture.M34
