import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.Reparametrization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Exhaustion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped ContDiff Manifold Topology

universe u

namespace PoincareConjecture.CylinderGluing

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_cylinder_of_relative_extensions (U : ℕ → Opens M)
    (F : ∀ n, Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (U n) ∞)
    (E : ℕ → Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞)
    (hretain : ∀ n (p : RoundCylinderSpace), p.2 ≤ 0 →
      (F (n + 1) ((E n).symm p) : M) = F n p)
    (hE : ∀ n (p : RoundCylinderSpace), p.2 ≤ 0 → ((E n).symm p).2 < 0)
    (hcover : ∀ x ∈ (⨆ n, U n : Opens M),
      ∃ (n : ℕ) (p : RoundCylinderSpace), p.2 ≤ 0 ∧ (F n p : M) = x) :
    ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace ↥(⨆ n, U n) ∞)
      (H : ℕ → Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞),
      H 0 = Diffeomorph.refl CylModel RoundCylinderSpace ∞ ∧
      (∀ n (p : RoundCylinderSpace), p.2 ≤ 0 → (D ((H n).symm p) : M) = F n p) ∧
      (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (D p : M) = F 0 p) := by
  obtain ⟨H, hH0, hHstep, hHcore⟩ := exists_exhausting_reparametrizations E hE
  let Dn (n : ℕ) := (H n).trans (F n)
  let S (n : ℕ) : Opens RoundCylinderSpace :=
    ⟨{p | (H n p).2 < 0}, isOpen_lt (continuous_snd.comp (H n).continuous) continuous_const⟩
  let V (n : ℕ) : Opens M :=
    ⟨(fun p : RoundCylinderSpace => (F n p : M)) '' {p | p.2 < 0},
      ((U n).isOpen.isOpenMap_subtype_val.comp (F n).toHomeomorph.isOpenMap) _
        (isOpen_lt continuous_snd continuous_const)⟩
  have hVU (n : ℕ) : (V n : Set M) ⊆ U n := by
    rintro x ⟨p, _, rfl⟩
    exact (F n p).property
  let j (n : ℕ) : V n → U n := fun y => ⟨y, hVU n y.property⟩
  have hj (n : ℕ) : ContMDiff (𝓡 3) (𝓡 3) ∞ (j n) := by
    rw [← ContMDiff.subtypeVal_comp_iff (U n)]
    exact contMDiff_subtype_val
  have hnegative (n : ℕ) (y : V n) : (H n ((Dn n).symm (j n y))).2 < 0 := by
    obtain ⟨p, hp, heq⟩ := y.property
    have hjp : j n y = F n p := Subtype.ext heq.symm
    change (H n ((H n).symm ((F n).symm (j n y)))).2 < 0
    rw [(H n).apply_symm_apply, hjp, (F n).symm_apply_apply]
    exact hp
  let e (n : ℕ) : Diffeomorph CylModel (𝓡 3) (S n) (V n) ∞ := {
    toFun := fun p => ⟨Dn n p, ⟨H n p, p.property, rfl⟩⟩
    invFun := fun y => ⟨(Dn n).symm (j n y), hnegative n y⟩
    left_inv := fun p => Subtype.ext ((Dn n).symm_apply_apply p)
    right_inv := by
      intro y
      apply Subtype.ext
      change (Dn n ((Dn n).symm (j n y)) : M) = y
      exact congrArg (fun z : U n => (z : M)) ((Dn n).apply_symm_apply (j n y))
    contMDiff_toFun := by
      rw [← ContMDiff.subtypeVal_comp_iff (V n)]
      change ContMDiff CylModel (𝓡 3) ∞ (fun p : S n => (Dn n p : M))
      exact contMDiff_subtype_val.comp ((Dn n).contMDiff.comp contMDiff_subtype_val)
    contMDiff_invFun := by
      rw [← ContMDiff.subtypeVal_comp_iff (S n)]
      change ContMDiff (𝓡 3) CylModel ∞ (fun y : V n => (Dn n).symm (j n y))
      exact (Dn n).symm.contMDiff.comp (hj n) }
  have hSmono : Monotone S := by
    apply monotone_nat_of_le_succ
    intro n p hp
    change (H n p).2 < 0 at hp
    change (H (n + 1) p).2 < 0
    rw [hHstep n p hp.le]
    exact hE n _ hp.le
  have hScover (p : RoundCylinderSpace) : ∃ n, p ∈ S n := by
    obtain ⟨n, hn⟩ := exists_nat_gt |p.2|
    exact ⟨n, hHcore n p hn⟩
  have hDstep (n : ℕ) (p : RoundCylinderSpace) (hp : p ∈ S n) :
      (Dn (n + 1) p : M) = Dn n p := by
    change (H n p).2 < 0 at hp
    change (F (n + 1) (H (n + 1) p) : M) = F n (H n p)
    rw [hHstep n p hp.le]
    exact hretain n _ hp.le
  have hDlater (n m : ℕ) (hnm : n ≤ m) (p : RoundCylinderSpace) (hp : p ∈ S n) :
      (Dn m p : M) = Dn n p := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih => exact (hDstep m p (hSmono hnm hp)).trans ih
  have heagree (n m : ℕ) (x : S n) (y : S m) (hxy : (x : RoundCylinderSpace) = y) :
      (e n x : M) = e m y := by
    change (Dn n x : M) = Dn m y
    rw [← hDlater n (max n m) (le_max_left _ _) x x.property,
      ← hDlater m (max n m) (le_max_right _ _) y y.property, hxy]
  have hVunion : (⨆ n, V n) = ⨆ n, U n := by
    apply le_antisymm
    · apply iSup_le
      intro n x hx
      exact Opens.mem_iSup.mpr ⟨n, hVU n hx⟩
    · intro x hx
      obtain ⟨n, p, hp, hpx⟩ := hcover x hx
      apply Opens.mem_iSup.mpr
      exact ⟨n + 1, (E n).symm p, hE n p hp, (hretain n p hp).trans hpx⟩
  obtain ⟨D, hD, _, _⟩ := Poincare.exists_diffeomorph_of_monotone_open_cover
    S V e hSmono hScover heagree
  have hpreserve (n : ℕ) (p : RoundCylinderSpace) (hp : p.2 ≤ 0) :
      (D ((H n).symm p) : M) = F n p := by
    let z := (H n).symm p
    have hz : (H n z).2 ≤ 0 := by simpa only [z, (H n).apply_symm_apply] using hp
    have hzin : z ∈ S (n + 1) := by
      change (H (n + 1) z).2 < 0
      rw [hHstep n z hz]
      exact hE n _ hz
    calc
      (D z : M) = e (n + 1) ⟨z, hzin⟩ := hD (n + 1) ⟨z, hzin⟩
      _ = F (n + 1) ((E n).symm p) := by
        change (F (n + 1) (H (n + 1) z) : M) = F (n + 1) ((E n).symm p)
        rw [hHstep n z hz]
        simp only [z, (H n).apply_symm_apply]
      _ = F n p := hretain n p hp
  have hfirst (p : RoundCylinderSpace) (hp : p.2 ≤ 0) : (D p : M) = F 0 p := by
    have h := hpreserve 0 p hp
    rw [hH0] at h
    exact h
  have hout : ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace ↥(⨆ n, V n) ∞)
      (H : ℕ → Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞),
      H 0 = Diffeomorph.refl CylModel RoundCylinderSpace ∞ ∧
      (∀ n (p : RoundCylinderSpace), p.2 ≤ 0 → (D ((H n).symm p) : M) = F n p) ∧
      (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (D p : M) = F 0 p) :=
    ⟨D, H, hH0, hpreserve, hfirst⟩
  rwa [hVunion] at hout

end PoincareConjecture.CylinderGluing
