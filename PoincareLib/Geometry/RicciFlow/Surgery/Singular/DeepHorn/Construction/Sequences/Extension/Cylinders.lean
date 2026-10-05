import PoincareLib.Geometry.RicciFlow.Surgery.Singular.Geometry

/-!
# Compatible cylinders in the supplied extension

Morgan--Tian Definition 3.38, printed p. 61, and Definition 9.78,
printed p. 232, require the actual clock and vertical curves. The old-slice
maps of the supplied extension transport those data without changing scale.

Read-only donors are `GeneralizedFlowCylinder.rebaseSource` and
`rebaseSource_pullbackInner` in `M48/CylinderSource.lean`, and
`GeneralizedFlowCylinder.time_mem_of_nonempty_source`,
`GeneralizedFlowExtension.oldSliceDiffeomorph`, `pushCylinder`,
`pushCylinder_pointMap`, and `pushCylinder_pullbackInner` in Horizon
`Surgery/Singular/DeepHorn/Neck/Extension.lean`. No donor proof is imported.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M32

variable {F : GeneralizedRicciFlowData.{u}}
  {C C' : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}

/-- A nonempty cylinder source forces each displayed clock value into the
actual flow interval, as required by Definition 9.78, printed p. 232. -/
theorem cylinder_time_mem_of_nonempty_source
    (d : GeneralizedFlowCylinder F C a q J U) (hC : Nonempty C.carrier)
    (s : ℝ) (hs : s ∈ J) : a + s / q ∈ F.interval :=
  (F.slice_nonempty_iff _).mp (hC.map (d.forward s hs))

/-- A fixed source diffeomorphism preserves the full compatible cylinder,
including its clock and vertical curves; Definition 9.78, printed p. 232. -/
noncomputable def rebaseCylinderSource (d : GeneralizedFlowCylinder F C a q J U)
    (f : Diffeomorph (𝓡 3) (𝓡 3) C'.carrier C.carrier ∞) :
    GeneralizedFlowCylinder F C' a q J (f ⁻¹' U) := by
  have hmaps : MapsTo f (f ⁻¹' U) U := fun _ hx => hx
  have himage (s : ℝ) (hs : s ∈ J) :
      (d.forward s hs ∘ f) '' (f ⁻¹' U) ⊆ d.forward s hs '' U := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨f x, hx, rfl⟩
  refine {
    scale_pos := d.scale_pos
    forward := fun s hs => d.forward s hs ∘ f
    inverse := fun s hs => f.symm ∘ d.inverse s hs
    forward_smooth := fun s hs => (d.forward_smooth s hs).comp f.contMDiff.contMDiffOn hmaps
    inverse_smooth := fun s hs =>
      f.symm.contMDiff.comp_contMDiffOn ((d.inverse_smooth s hs).mono (himage s hs))
    left_inverse := ?_
    right_inverse := ?_
    embedding := d.embedding.comp
      (Topology.IsEmbedding.id.prodMap (f.toHomeomorph.isEmbedding.restrict hmaps))
    vertical_compatibility := fun s hs x hx => d.vertical_compatibility s hs (f x) hx }
  · intro s hs x hx
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs hx, f.symm_apply_apply]
  · intro s hs y hy
    rcases hy with ⟨x, hx, rfl⟩
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs hx, f.apply_symm_apply]

/-- On an open source, fixed reparameterization pulls back the actual
scaled metric by its derivative; Definition 9.78, printed p. 232. -/
theorem rebaseCylinderSource_pullbackInner
    (d : GeneralizedFlowCylinder F C a q J U)
    (f : Diffeomorph (𝓡 3) (𝓡 3) C'.carrier C.carrier ∞)
    (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    (x : C'.carrier) (hx : f x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (rebaseCylinderSource d f).pullbackInner s hs x v w =
      d.pullbackInner s hs (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  have hd := ((d.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hf := f.contMDiff.mdifferentiable (by simp) x
  dsimp only [GeneralizedFlowCylinder.pullbackInner, rebaseCylinderSource]
  rw [mfderiv_comp x hd hf]
  rfl

variable {T : ℝ} (E : GeneralizedFlowExtension F T)

/-- The supplied old-slice maps form a diffeomorphism at the unchanged
clock value, as used in Claim 11.32, printed pp. 287-288. -/
noncomputable def extension_oldSliceDiffeomorph (t : ℝ) (ht : t ∈ F.interval) :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice t).carrier (E.extended.slice t).carrier ∞ where
  toFun := E.forward t ht
  invFun := E.inverse t ht
  left_inv := E.left_inverse t ht
  right_inv := E.right_inverse t ht
  contMDiff_toFun := E.forward_smooth t ht
  contMDiff_invFun := E.inverse_smooth t ht

/-- The extension transports every point and vertical curve of the old
cylinder with its original clock and scale; Definition 9.78, p. 232. -/
noncomputable def extension_pushCylinder (d : GeneralizedFlowCylinder F C a q J U)
    (hC : Nonempty C.carrier) : GeneralizedFlowCylinder E.extended C a q J U := by
  let f (s : ℝ) (hs : s ∈ J) := extension_oldSliceDiffeomorph E (a + s / q)
    (cylinder_time_mem_of_nonempty_source d hC s hs)
  refine {
    scale_pos := d.scale_pos
    forward := fun s hs => f s hs ∘ d.forward s hs
    inverse := fun s hs => d.inverse s hs ∘ (f s hs).symm
    forward_smooth := fun s hs => (f s hs).contMDiff.comp_contMDiffOn (d.forward_smooth s hs)
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    embedding := ?_
    vertical_compatibility := ?_ }
  · intro s hs
    apply (d.inverse_smooth s hs).comp (f s hs).symm.contMDiff.contMDiffOn
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  · intro s hs x hx
    simpa only [Function.comp_apply, Diffeomorph.symm_apply_apply] using d.left_inverse s hs hx
  · intro s hs y hy
    obtain ⟨x, hx, rfl⟩ := hy
    dsimp only [Function.comp_apply]
    rw [Diffeomorph.symm_apply_apply, d.left_inverse s hs hx]
  · have heq : (fun p : J × U =>
        (⟨a + p.1.1 / q, f p.1.1 p.1.2 (d.forward p.1.1 p.1.2 p.2.1)⟩ : E.extended.point)) =
        E.spacetime_forward ∘ (fun p : J × U =>
          (⟨a + p.1.1 / q, d.forward p.1.1 p.1.2 p.2.1⟩ : F.point)) := by
      funext p
      exact (E.spacetime_slices _ (cylinder_time_mem_of_nonempty_source d hC p.1.1 p.1.2) _).symm
    change Topology.IsEmbedding (fun p : J × U =>
      (⟨a + p.1.1 / q, f p.1.1 p.1.2 (d.forward p.1.1 p.1.2 p.2.1)⟩ : E.extended.point))
    rw [heq]
    exact E.spacetime_openEmbedding.isEmbedding.comp d.embedding
  · intro s hs x hx
    obtain ⟨b, y, r, hr, hworld⟩ := d.vertical_compatibility s hs x hx
    obtain ⟨hb, _⟩ := hworld s hs (by simpa using hr)
    obtain ⟨c, z, r', hr', hworld'⟩ := E.vertical_compatibility b (a + s / q) hb y
    refine ⟨c, z, min r (r' * q), lt_min hr (mul_pos hr' d.scale_pos), ?_⟩
    intro s' hs' hdist
    obtain ⟨hb', hby'⟩ := hworld s' hs' (hdist.trans_le (min_le_left _ _))
    have hphysical : |(a + s' / q) - (a + s / q)| < r' := by
      rw [show (a + s' / q) - (a + s / q) = (s' - s) / q by ring,
        abs_div, abs_of_pos d.scale_pos]
      exact (div_lt_iff₀ d.scale_pos).mpr (hdist.trans_le (min_le_right _ _))
    obtain ⟨hc, hcz⟩ := hworld' (a + s' / q) hb' hphysical
    refine ⟨hc, ?_⟩
    rw [E.spacetime_slices _ (cylinder_time_mem_of_nonempty_source d hC s' hs') _] at hcz
    change E.forward (a + s' / q) _ (d.forward s' hs' x) = _
    rw [hby']
    exact eq_of_heq (Sigma.mk.inj hcz).2

/-- Every transported cylinder point is the image of its actual old
spacetime point, as required in Definition 9.78, printed p. 232. -/
theorem extension_pushCylinder_pointMap (d : GeneralizedFlowCylinder F C a q J U)
    (hC : Nonempty C.carrier) (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (extension_pushCylinder E d hC).pointMap s hs x =
      E.spacetime_forward (d.pointMap s hs x) :=
  (E.spacetime_slices _ (cylinder_time_mem_of_nonempty_source d hC s hs) _).symm

/-- The transported cylinder has the identical pulled-back metric on its
open source, retaining the comparison of Definition 9.78, printed p. 232. -/
theorem extension_pushCylinder_pullbackInner (d : GeneralizedFlowCylinder F C a q J U)
    (hC : Nonempty C.carrier) (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    (x : C.carrier) (hx : x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (extension_pushCylinder E d hC).pullbackInner s hs x v w =
      d.pullbackInner s hs x v w := by
  let f := extension_oldSliceDiffeomorph E (a + s / q)
    (cylinder_time_mem_of_nonempty_source d hC s hs)
  have hd := ((d.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hf := f.contMDiff.mdifferentiable (by simp) (d.forward s hs x)
  change q * (E.extended.metric (a + s / q)).inner (f (d.forward s hs x))
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ d.forward s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ d.forward s hs) x w) = _
  rw [mfderiv_comp x hf hd]
  change q * (E.extended.metric (a + s / q)).inner (E.forward _ _ (d.forward s hs x))
      (mfderiv (𝓡 3) (𝓡 3) (E.forward _ _) (d.forward s hs x)
        (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x v))
      (mfderiv (𝓡 3) (𝓡 3) (E.forward _ _) (d.forward s hs x)
        (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x w)) = _
  rw [E.metric_pullback]
  rfl

end PoincareMT.M32
