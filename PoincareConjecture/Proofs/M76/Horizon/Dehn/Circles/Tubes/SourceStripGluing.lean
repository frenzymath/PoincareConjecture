import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalSourceStrips
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PrismCycle

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem exists_source_strip_gluing
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} (f : E → X) (physical : P2 → X)
    {n : ℕ} (t : Fin (n + 3) → ℝ) (ht : StrictMono t)
    (localMap : Fin (n + 2) → P2 → E)
    (hPL : ∀ k, FinitePiecewiseAffineOn (localMap k)
      (Icc (-1 : ℝ) 1 ×ˢ Icc (t k.castSucc) (t k.succ)))
    (hD : ∀ k, MapsTo (localMap k)
      (Icc (-1 : ℝ) 1 ×ˢ Icc (t k.castSucc) (t k.succ)) U)
    (hvalue : ∀ k z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t k.castSucc) (t k.succ) →
      f (localMap k z) = physical z)
    (hunique : ∀ k z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t k.castSucc) (t k.succ) →
      z.1 ≠ 0 → ∀ w ∈ U, f w = physical z → w = localMap k z) :
    ∃ phi : P2 → E,
      FinitePiecewiseAffineOn phi (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) ∧
      (∀ k z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t k.castSucc) (t k.succ) →
        phi z = localMap k z) ∧
      MapsTo phi (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) U ∧
      ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))),
        f (phi z) = physical z := by
  classical
  let S (k : Fin (n + 2)) := Icc (-1 : ℝ) 1 ×ˢ Icc (t k.castSucc) (t k.succ)
  have hagree (k l : Fin (n + 2)) (z : P2) (hk : z ∈ S k) (hl : z ∈ S l) :
      localMap k z = localMap l z := by
    have hc (v : Fin (n + 2)) (hv : z.2 ∈ Icc (t v.castSucc) (t v.succ)) :
        ContinuousOn (fun u : ℝ => localMap v (u, z.2)) (Icc (-1 : ℝ) 1) :=
      (hPL v).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ hu => ⟨hu, hv⟩)
    have heq := eqOn_transverse_interval_of_eq_ne_zero (by norm_num : (0 : ℝ) < 1)
      (hc k hk.2) (hc l hl.2) (fun u hu hne =>
        hunique l (u, z.2) ⟨hu, hl.2⟩ hne (localMap k (u, z.2))
          (hD k ⟨hu, hk.2⟩) (hvalue k _ ⟨hu, hk.2⟩))
    exact heq hk.1
  let phi : P2 → E := fun z => if hz : z ∈ ⋃ k, S k then
    localMap (mem_iUnion.mp hz).choose z else 0
  have hval (k : Fin (n + 2)) (z : P2) (hz : z ∈ S k) : phi z = localMap k z := by
    have hz' : z ∈ ⋃ k, S k := mem_iUnion.mpr ⟨k, hz⟩
    dsimp only [phi]
    rw [dif_pos hz']
    exact hagree _ k z (mem_iUnion.mp hz').choose_spec hz
  have hsource : (⋃ k, S k) = Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨k, hk⟩ := mem_iUnion.mp hz
      exact ⟨hk.1, (ht.monotone (Fin.zero_le _)).trans hk.2.1,
        hk.2.2.trans (ht.monotone (Fin.le_last _))⟩
    · intro hz
      obtain ⟨k, hk⟩ := ht.monotone.exists_mem_consecutive_Icc hz.2
      exact mem_iUnion.mpr ⟨k, hz.1, hk⟩
  have hphiPL : FinitePiecewiseAffineOn phi (⋃ k, S k) :=
    FinitePiecewiseAffineOn.iUnion (fun k => (hPL k).congr
      (fun z hz => (hval k z hz).symm))
  refine ⟨phi, hsource ▸ hphiPL, hval, ?_, ?_⟩
  · intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hsource.symm.subset hz)
    rw [hval k z hk]
    exact hD k hk
  · intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hsource.symm.subset hz)
    rw [hval k z hk]
    exact hvalue k z hk

end PoincareConjecture.M76.Dehn
