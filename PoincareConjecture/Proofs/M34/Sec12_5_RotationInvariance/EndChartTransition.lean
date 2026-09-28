import PoincareConjecture.Proofs.M34.Mathlib.OpenDomainMap
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndTranslationCalculus










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)



def endReferenceOverlap (r : ℝ) : Set (endReferenceRegion e) :=
  {x | endAxialTranslation e r x ∈ endReferenceRegion e}



theorem endReferenceOverlap_isOpen (r : ℝ) (hr : -3 < r) :
    IsOpen (endReferenceOverlap e r) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  exact (endReferenceRegion_isOpen e).preimage
    (endReferenceTranslation_isLocalDiffeomorph e hr).contMDiff.continuous



noncomputable def endReferenceTransition (p : endReferenceRegion e) (r : ℝ) :
    endReferenceRegion e → endReferenceRegion e :=
  letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  fun x => (extChartAt (𝓡 3) p).symm (endAxialTranslation e r x)



theorem endReferenceTransition_coe (p : endReferenceRegion e) (r : ℝ)
    {x : endReferenceRegion e} (hx : x ∈ endReferenceOverlap e r) :
    (endReferenceTransition e p r x : StandardCapSpace) = endAxialTranslation e r x :=
  canonicalOpen_map_coe (𝕜 := ℝ) (endReferenceRegion_isOpen e)
    (endAxialTranslation e r) p x hx



theorem endReferenceTransition_contMDiffOn (p : endReferenceRegion e)
    (r : ℝ) (hr : -3 < r) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (endReferenceTransition e p r) (endReferenceOverlap e r) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro x hx
  have hf := (endReferenceTranslation_contMDiffOn e hr x x.property).contMDiffAt
    ((endReferenceRegion_isOpen e).mem_nhds x.property)
  exact (canonicalOpen_map_contMDiffAt (endReferenceRegion_isOpen e)
    (endReferenceRegion_isOpen e) hf hx p).contMDiffWithinAt



theorem endReferenceTransition_mfderiv (p : endReferenceRegion e)
    (r : ℝ) (hr : -3 < r) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ x : endReferenceRegion e, x ∈ endReferenceOverlap e r →
      mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) x =
        mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) (x : StandardCapSpace) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro x hx
  have hf := ((endReferenceTranslation_contMDiffOn e hr x x.property).contMDiffAt
    ((endReferenceRegion_isOpen e).mem_nhds x.property)).mdifferentiableAt (by simp)
  exact canonicalOpen_map_mfderiv (endReferenceRegion_isOpen e)
    (endReferenceRegion_isOpen e) hf hx p



theorem endReferenceTransition_metric {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (p : endReferenceRegion e) (r : ℝ) (hr : -3 < r) (s : ℝ) (hs : -3 < s)
    (hrs : -3 < r + s) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ) (x : endReferenceRegion e), x ∈ endReferenceOverlap e r →
      ∀ u v : TangentSpace (𝓡 3) x,
        ((endPullbackFlow e F (r + s) hrs).metric t).inner x u v =
          ((endPullbackFlow e F s hs).metric t).inner (endReferenceTransition e p r x)
            (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) x u)
            (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) x v) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t x hx u v
  rw [endPullbackFlow_inner e F (r + s) hrs,
    endPullbackFlow_inner e F s hs, endReferenceTransition_mfderiv e p r hr x hx]
  change (F.metric t).inner (endAxialTranslation e (r + s) x)
    (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e (r + s)) x u)
    (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e (r + s)) x v) =
      (F.metric t).inner (endAxialTranslation e s (endReferenceTransition e p r x))
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) (endReferenceTransition e p r x)
          (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x u))
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) (endReferenceTransition e p r x)
          (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x v))
  rw [endReferenceTransition_coe e p r hx,
    endAxialTranslation_comp_reference e r hr s x.property,
    endAxialTranslation_mfderiv_comp_reference e r hr s hs x.property hx]
  rfl

end PoincareConjecture.M34
