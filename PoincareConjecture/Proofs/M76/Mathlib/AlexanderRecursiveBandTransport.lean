import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveRemainderTransport
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineSlabComplex
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {S : Set E} {T : Set V} {F : S ≃ₜ T}

omit [FiniteDimensional ℝ V] in




theorem IsFinitePL.exists_affineBand_restriction (hF : F.IsFinitePL)
    (A : E →ᵃ[ℝ] ℝ) (B : V →ᵃ[ℝ] ℝ)
    (hheight : ∀ x : S, B (F x) = A x) (a b : ℝ) :
    ∃ G : (S ∩ {x | A x ∈ Icc a b} : Set E) ≃ₜ
        (T ∩ {y | B y ∈ Icc a b} : Set V), G.IsFinitePL ∧
      (∀ x, (G x : V) = F ⟨x, x.property.1⟩) ∧
      ∀ x, B (G x) = A x := by
  have hcopy := hF
  obtain ⟨_, ⟨K, hK, hKS, _⟩, _⟩ := hcopy
  obtain ⟨J, hJ, hJS⟩ := K.exists_finite_affineSlab_complex hK A a b
  rw [hKS] at hJS
  have hmem (x : S) : (x : E) ∈ S ∩ {x | A x ∈ Icc a b} ↔
      (F x : V) ∈ T ∩ {y | B y ∈ Icc a b} := by
    simp only [mem_inter_iff, mem_ofPred_eq, x.property, (F x).property,
      true_and, hheight x]
  let G := F.restrictSubsets inter_subset_left inter_subset_left hmem
  exact ⟨G, hF.restrictSubsets inter_subset_left inter_subset_left hmem J hJ hJS,
    fun _ => rfl, fun x => hheight ⟨x, x.property.1⟩⟩

omit [FiniteDimensional ℝ V] in




theorem IsFinitePL.exists_affineLevel_restriction (hF : F.IsFinitePL)
    (A : E →ᵃ[ℝ] ℝ) (B : V →ᵃ[ℝ] ℝ)
    (hheight : ∀ x : S, B (F x) = A x) (a : ℝ) :
    ∃ G : (S ∩ {x | A x = a} : Set E) ≃ₜ (T ∩ {y | B y = a} : Set V),
      G.IsFinitePL ∧ ∀ x, (G x : V) = F ⟨x, x.property.1⟩ := by
  have hcopy := hF
  obtain ⟨_, ⟨K, hK, hKS, _⟩, _⟩ := hcopy
  obtain ⟨J, hJ, hJS⟩ := K.exists_finite_affineLevel_complex hK A a
  rw [hKS] at hJS
  have hmem (x : S) : (x : E) ∈ S ∩ {x | A x = a} ↔
      (F x : V) ∈ T ∩ {y | B y = a} := by
    simp only [mem_inter_iff, mem_ofPred_eq, x.property, (F x).property,
      true_and, hheight x]
  exact ⟨F.restrictSubsets inter_subset_left inter_subset_left hmem,
    hF.restrictSubsets inter_subset_left inter_subset_left hmem J hJ hJS,
    fun _ => rfl⟩






theorem IsFinitePL.exists_regularSlab_transport (hF : F.IsFinitePL)
    (A : E →ᵃ[ℝ] ℝ) (B : V →ᵃ[ℝ] ℝ)
    (hheight : ∀ x : S, B (F x) = A x) {a b : ℝ} (hab : a < b)
    (C : ((S ∩ {x | A x = a}) ×ˢ Icc a b : Set (E × ℝ)) ≃ₜ
      (S ∩ {x | A x ∈ Icc a b} : Set E))
    (hC : C.IsFinitePL) (hCheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hCbase : ∀ (x : E) (hx : x ∈ S ∩ {x | A x = a}),
      (C ⟨(x, a), ⟨hx, ⟨le_rfl, hab.le⟩⟩⟩ : E) = x) :
    ∃ G : ((T ∩ {y | B y = a}) ×ˢ Icc a b : Set (V × ℝ)) ≃ₜ
        (T ∩ {y | B y ∈ Icc a b} : Set V), G.IsFinitePL ∧
      (∀ p, B (G p) = (p : V × ℝ).2) ∧
      ∀ (y : V) (hy : y ∈ T ∩ {y | B y = a}),
        (G ⟨(y, a), ⟨hy, ⟨le_rfl, hab.le⟩⟩⟩ : V) = y := by
  obtain ⟨D, hD, hDval, hDheight⟩ := hF.exists_affineBand_restriction A B hheight a b
  obtain ⟨d, hd, hdval⟩ := hF.exists_affineLevel_restriction A B hheight a
  have hinterval := isFinitePLBallPair_Icc hab
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJI, _⟩, _⟩, _⟩ := hinterval
  have hid : (Homeomorph.refl (Icc a b)).IsFinitePL :=
    ⟨id, ⟨J, hJ, hJI, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩,
      fun _ => rfl⟩
  let P := (Homeomorph.Set.prod (T ∩ {y | B y = a}) (Icc a b)).trans
    ((d.symm.prodCongr (Homeomorph.refl (Icc a b))).trans
      (Homeomorph.Set.prod (S ∩ {x | A x = a}) (Icc a b)).symm)
  let G := P.trans (C.trans D)
  refine ⟨G, (hd.symm.prod hid).trans (hC.trans hD), ?_, ?_⟩
  · intro p
    exact (hDheight (C (P p))).trans (hCheight (P p))
  · intro y hy
    let p : ((T ∩ {y | B y = a}) ×ˢ Icc a b : Set (V × ℝ)) :=
      ⟨(y, a), ⟨hy, ⟨le_rfl, hab.le⟩⟩⟩
    let x := d.symm ⟨y, hy⟩
    have hC0 : (C (P p) : E) = x := hCbase x x.property
    change (D (C (P p)) : V) = y
    calc
      (D (C (P p)) : V) = F ⟨C (P p), (C (P p)).property.1⟩ := hDval _
      _ = F ⟨x, x.property.1⟩ := congrArg (fun z : S => (F z : V)) (Subtype.ext hC0)
      _ = d x := (hdval x).symm
      _ = y := congrArg Subtype.val (d.apply_symm_apply ⟨y, hy⟩)

end Homeomorph
