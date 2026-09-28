import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.MarkedDisplacementExtension
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.LocalPLScalarArithmetic

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open scoped BigOperators

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_finite_annulus_displacement_extension
    {X ι η : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [Fintype η]
    (e : ι → OpenPartialHomeomorph X V3)
    {R : Set X} (heR : PLDomain e R)
    (j : η → (ℝ × ℝ) → X) (hj : ∀ i, PolyhedralPLInCharts e (j i) Ann)
    (hji : ∀ i, Topology.IsEmbedding (fun z : Ann => j i z))
    (hjR : ∀ i, MapsTo (j i) Ann R)
    (hrim : ∀ i, ∀ z : Ann,
      depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔ j i z ∈ frontier R)
    (hdis : Pairwise (fun i k => Disjoint (j i '' Ann) (j k '' Ann)))
    (w : η → (ℝ × ℝ) → V3) (hw : ∀ i, FinitePiecewiseAffineOn (w i) Ann)
    (hw1 : ∀ i, ∀ x ∈ Ann, w i x 1 = 0)
    (hwzero : ∀ i, ∀ z : Ann,
      depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 → w i z = 0) :
    ∃ W : C(X, V3),
      (∀ i, LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target) ∧
      (∀ i, ∀ z : Ann, W (j i z) = w i z) ∧
      (∀ x ∉ interior R, W x = 0) ∧ (∀ x, W x 1 = 0) := by
  classical
  let S (i : η) := j i '' Ann
  have hS (i : η) : IsCompact (S i) :=
    (hw i).isCompact.image_of_continuousOn (hj i).continuousOn
  let U (i : η) := (⋃ k : {k : η // k ≠ i}, S k)ᶜ
  have hU (i : η) : IsOpen (U i) :=
    (isClosed_iUnion_of_finite (fun k : {k : η // k ≠ i} => (hS k).isClosed)).isOpen_compl
  have hjU (i : η) (z : Ann) : j i z ∈ U i := by
    intro hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    exact disjoint_left.mp (hdis k.property.symm) ⟨z, z.property, rfl⟩ hk
  have hex (i : η) := exists_original_retained_annulus_displacement_extension_within
    e heR (hj i) (hji i) (hjR i) (hrim i) (w i) (hw i) (hw1 i) (hwzero i)
    (U i) (hU i) (hjU i)
  choose V hVPL hVbase hVfront hV1 hVout hVU using hex
  let W : C(X, V3) := ∑ i, V i
  have hW (x : X) : W x = ∑ i, V i x := by simp [W]
  have hVother (i k : η) (hik : k ≠ i) (z : Ann) : V k (j i z) = 0 := by
    apply hVU k
    intro hx
    exact hx (mem_iUnion.mpr ⟨⟨i, hik.symm⟩, ⟨z, z.property, rfl⟩⟩)
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro a
    apply LocallyPiecewiseAffineOn.pi (e a).open_target
    intro k
    have hcoord (i : η) : LocallyPiecewiseAffineOn
        (fun z => V i ((e a).symm z) k) (e a).target := by
      have h := (locallyPiecewiseAffineOn_affine
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) k).toContinuousAffineMap
        isOpen_univ).comp (hVPL i a)
      rw [preimage_univ, inter_univ] at h
      exact h.congr (fun _ _ => rfl)
    have hsum := locallyPiecewiseAffineOn_finset_sum Finset.univ (e a).open_target
      (fun i z => V i ((e a).symm z) k) (fun i _ => hcoord i)
    apply hsum.congr
    intro z _
    simp [W]
  · intro i z
    rw [hW, Finset.sum_eq_single i]
    · exact hVbase i z
    · intro k _ hki
      exact hVother i k hki z
    · simp
  · intro x hx
    rw [hW]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hxR : x ∈ R
    · exact hVfront i x ⟨subset_closure hxR, hx⟩
    · exact hVout i x hxR
  · intro x
    rw [hW]
    simp only [Finset.sum_apply, hV1, Finset.sum_const_zero]

end PoincareConjecture.M76
