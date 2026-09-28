import PoincareConjecture.Proofs.M76.Mathlib.AffineHyperplaneCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.OpenPartialHomeomorph.IsImage











set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]




theorem isImage_frontier_of_affine_nonneg (H : OpenPartialHomeomorph X E)
    {K : Set X} (ell : E →ᴬ[ℝ] ℝ) (hell : ell.toAffineMap.linear ≠ 0)
    (hhalf : ∀ x ∈ H.source, x ∈ K ↔ 0 ≤ ell (H x)) :
    H.IsImage (frontier K) {z | ell z = 0} := by
  have hopen : IsOpenMap (ell : E → ℝ) := ell.toAffineMap.isOpenMap ell.continuous
    (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hell))
  have hfront : frontier {z | 0 ≤ ell z} = {z | ell z = 0} := by
    change frontier ((ell : E → ℝ) ⁻¹' Ici 0) = (ell : E → ℝ) ⁻¹' {0}
    rw [← hopen.preimage_frontier_eq_frontier_preimage ell.continuous, frontier_Ici]
  have himage : H.IsImage K {z | 0 ≤ ell z} := fun {x} hx => (hhalf x hx).symm
  simpa only [hfront] using himage.frontier

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in





theorem exists_affine_hypersurface_chart (H : OpenPartialHomeomorph X E)
    {B : Set X} (ell : E →ᴬ[ℝ] ℝ) (himage : H.IsImage B {z | ell z = 0})
    (a : F →ᴬ[ℝ] E) (r : E →ᴬ[ℝ] F)
    (hra : Function.LeftInverse r a) (har : LeftInvOn a r {z | ell z = 0})
    (haz : ∀ z, ell (a z) = 0) (b : B) :
    ∃ q : OpenPartialHomeomorph B F,
      q.source = Subtype.val ⁻¹' H.source ∧ q.target = a ⁻¹' H.target ∧
      (∀ x : B, q x = r (H x)) ∧
      ∀ z ∈ q.target, (q.symm z : X) = H.symm (a z) := by
  classical
  let f : B → F := fun x => r (H x)
  let g : F → B := fun z => if hz : a z ∈ H.target then
    ⟨H.symm (a z), (himage.symm_apply_mem_iff hz).mpr (haz z)⟩ else b
  have hg (z : F) (hz : a z ∈ H.target) : (g z : X) = H.symm (a z) := by
    simp only [g, dif_pos hz]
  have hmap : MapsTo f (Subtype.val ⁻¹' H.source) (a ⁻¹' H.target) := by
    intro x hx
    change a (r (H x)) ∈ H.target
    rw [har ((himage.apply_mem_iff hx).mpr x.property)]
    exact H.map_source hx
  have hinvmap : MapsTo g (a ⁻¹' H.target) (Subtype.val ⁻¹' H.source) := by
    intro z hz
    change (g z : X) ∈ H.source
    rw [hg z hz]
    exact H.map_target hz
  have hleft : LeftInvOn g f (Subtype.val ⁻¹' H.source) := by
    intro x hx
    apply Subtype.ext
    rw [hg (f x) (hmap hx)]
    change H.symm (a (r (H x))) = (x : X)
    rw [har ((himage.apply_mem_iff hx).mpr x.property), H.left_inv hx]
  have hright : LeftInvOn f g (a ⁻¹' H.target) := by
    intro z hz
    change r (H (g z : X)) = z
    rw [hg z hz, H.right_inv hz, hra z]
  have hf : ContinuousOn f (Subtype.val ⁻¹' H.source) :=
    r.continuous.comp_continuousOn
      (H.continuousOn_toFun.comp continuous_subtype_val.continuousOn (fun _ hx => hx))
  have hgc : ContinuousOn g (a ⁻¹' H.target) := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact (H.continuousOn_invFun.comp a.continuous.continuousOn (fun _ hz => hz)).congr
      (fun z hz => hg z hz)
  let q : OpenPartialHomeomorph B F :=
    { toFun := f
      invFun := g
      source := Subtype.val ⁻¹' H.source
      target := a ⁻¹' H.target
      map_source' := hmap
      map_target' := hinvmap
      left_inv' := hleft
      right_inv' := hright
      open_source := H.open_source.preimage continuous_subtype_val
      open_target := H.open_target.preimage a.continuous
      continuousOn_toFun := hf
      continuousOn_invFun := hgc }
  exact ⟨q, rfl, rfl, fun _ => rfl, hg⟩





theorem affine_hypersurface_transition_mem
    {B : Set X} (H H' : OpenPartialHomeomorph X E)
    (q q' : OpenPartialHomeomorph B F) (a : F →ᴬ[ℝ] E) (r' : E →ᴬ[ℝ] F)
    (hsource : q'.source = Subtype.val ⁻¹' H'.source)
    (htarget : q.target = a ⁻¹' H.target)
    (hforward : ∀ x : B, q' x = r' (H' x))
    (hinverse : ∀ z ∈ q.target, (q.symm z : X) = H.symm (a z))
    (hPL : H.symm.trans H' ∈ piecewiseAffineGroupoid E) :
    q.symm.trans q' ∈ piecewiseAffineGroupoid F := by
  let T := H.symm.trans H'
  let D := (q.symm.trans q').source
  have hD : IsOpen D := (q.symm.trans q').open_source
  have hsub : D ⊆ univ ∩ a ⁻¹' T.source := by
    intro z hz
    have ht : a z ∈ H.target := by
      change z ∈ a ⁻¹' H.target
      rw [← htarget]
      exact hz.1
    have hs : (q.symm z : X) ∈ H'.source := by
      change q.symm z ∈ Subtype.val ⁻¹' H'.source
      rw [← hsource]
      exact hz.2
    rw [hinverse z hz.1] at hs
    exact ⟨mem_univ z, ht, hs⟩
  have hT : LocallyPiecewiseAffineOn T T.source :=
    ((mem_piecewiseAffineGroupoid_iff E _).mp hPL).1
  have hbase := (hT.comp (locallyPiecewiseAffineOn_affine a isOpen_univ)).mono hD hsub
  have hcomp := ((locallyPiecewiseAffineOn_affine r' isOpen_univ).comp hbase).mono hD
    (fun z hz => ⟨hz, mem_univ _⟩)
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  apply hcomp.congr
  intro z hz
  change r' (H' (H.symm (a z))) = q' (q.symm z)
  rw [hforward (q.symm z), hinverse z hz.1]

end OpenPartialHomeomorph
