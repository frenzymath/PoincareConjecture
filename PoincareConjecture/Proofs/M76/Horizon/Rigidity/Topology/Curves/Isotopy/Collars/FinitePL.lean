import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.Extension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMinimum
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall









set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def collarTrack (track : (ℝ × E) → E) (t : ℝ) (z : ℝ × E) : ℝ × E :=
  (z.1, track (min t (1 - z.1), z.2))

theorem finitePiecewiseAffineOn_collarTrack
    {A : Set E} (track : (ℝ × E) → E)
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ A)) (t : I) :
    FinitePiecewiseAffineOn (collarTrack track t) (Icc (0 : ℝ) 1 ×ˢ A) := by
  obtain ⟨K, hK, hKs, hfaces⟩ := htrack
  have htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ A) :=
    ⟨K, hK, hKs, hfaces⟩
  have hfst : FinitePiecewiseAffineOn (fun z : ℝ × E => z.1)
      (Icc (0 : ℝ) 1 ×ˢ A) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine
      (ContinuousLinearMap.fst ℝ ℝ E).toContinuousAffineMap⟩
  have hsnd : FinitePiecewiseAffineOn (fun z : ℝ × E => z.2)
      (Icc (0 : ℝ) 1 ×ˢ A) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine
      (ContinuousLinearMap.snd ℝ ℝ E).toContinuousAffineMap⟩
  have hconst (c : ℝ) : FinitePiecewiseAffineOn (fun _ : ℝ × E => c)
      (Icc (0 : ℝ) 1 ×ˢ A) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.const ℝ (ℝ × E) c)⟩
  have hparameter : FinitePiecewiseAffineOn
      (fun z : ℝ × E => (min (t : ℝ) (1 - z.1), z.2)) (Icc (0 : ℝ) 1 ×ˢ A) :=
    ((hconst t).min ((hconst 1).sub hfst)).prod_mk hsnd
  have hmaps : MapsTo (fun z : ℝ × E => (min (t : ℝ) (1 - z.1), z.2))
      (Icc (0 : ℝ) 1 ×ˢ A) (Icc (0 : ℝ) 1 ×ˢ A) := by
    intro z hz
    exact ⟨⟨le_min t.property.1 (sub_nonneg.mpr hz.1.2),
      (min_le_left _ _).trans t.property.2⟩, hz.2⟩
  exact hfst.prod_mk (htrack.comp hparameter hmaps)


def collarExtensionOnCarrier {A : Set E} (H : I → A ≃ₜ A)
    (hc : Continuous (fun z : I × A => H z.1 z.2))
    (hci : Continuous (fun z : I × A => (H z.1).symm z.2)) (t : I) :
    (Icc (0 : ℝ) 1 ×ˢ A) ≃ₜ (Icc (0 : ℝ) 1 ×ˢ A) :=
  (Homeomorph.Set.prod (Icc (0 : ℝ) 1) A).trans
    ((collarExtension H hc hci t).trans (Homeomorph.Set.prod (Icc (0 : ℝ) 1) A).symm)

theorem isFinitePL_collarExtensionOnCarrier
    {A : Set E} (H : I → A ≃ₜ A)
    (hc : Continuous (fun z : I × A => H z.1 z.2))
    (hci : Continuous (fun z : I × A => (H z.1).symm z.2))
    (track : (ℝ × E) → E)
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ A))
    (hvalue : ∀ t : I, ∀ x : A, track ((t : ℝ), x) = (H t x : E)) (t : I) :
    (collarExtensionOnCarrier H hc hci t).IsFinitePL := by
  refine ⟨collarTrack track t, finitePiecewiseAffineOn_collarTrack track htrack t, ?_⟩
  intro x
  exact Prod.ext rfl (hvalue (cutoff t ⟨(x : ℝ × E).1, x.property.1⟩)
    ⟨(x : ℝ × E).2, x.property.2⟩).symm

theorem isFinitePL_collarExtensionOnCarrier_symm
    {A : Set E} (H : I → A ≃ₜ A)
    (hc : Continuous (fun z : I × A => H z.1 z.2))
    (hci : Continuous (fun z : I × A => (H z.1).symm z.2))
    (track : (ℝ × E) → E)
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ A))
    (hvalue : ∀ t : I, ∀ x : A, track ((t : ℝ), x) = (H t x : E)) (t : I) :
    (collarExtensionOnCarrier H hc hci t).symm.IsFinitePL :=
  (isFinitePL_collarExtensionOnCarrier H hc hci track htrack hvalue t).symm

end PoincareConjecture.M76.CollarIsotopy
