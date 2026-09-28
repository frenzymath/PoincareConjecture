import PoincareConjecture.Proofs.M76.Rigidity.MeridianCutFrontierMap









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

variable {ι : Type*} {e : ι → OpenPartialHomeomorph X V3} {j : V2 → X}



theorem meridianCutFrontierMap_frontier_iff (P : OriginalDiskProduct e R j)
    {a : ℝ} (hgap : a / 2 < p - a / 2)
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t))
    (z : E) (hz : z ∈ cubePrismBoundary (a / 2) (p - a / 2)) :
    P.meridianCutFrontierMap a z ∈ frontier R ↔ z.1 ∈ Q := by
  rcases hz with hlat | hcap
  · rw [P.meridianCutFrontierMap_lateral hgap hmark z hlat.1]
    rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    change (z.1 ∈ Q ∧ True) ↔ z.1 ∈ Q
    simp only [and_true]
  · have ht : z.2 = a / 2 ∨ z.2 = p - a / 2 := hcap.2
    rcases ht with ht | ht
    · have hz' : z = (z.1, a / 2) := Prod.ext rfl ht
      rw [hz', P.meridianCutFrontierMap_lower]
      exact P.proper (z.1, (1 / 2 : ℝ)) ⟨hcap.1, by norm_num⟩
    · have hz' : z = (z.1, p - a / 2) := Prod.ext rfl ht
      rw [hz', P.meridianCutFrontierMap_upper hgap]
      exact P.proper (z.1, -(1 / 2 : ℝ)) ⟨hcap.1, by norm_num⟩

private theorem injective_on_caps (P : OriginalDiskProduct e R j)
    {a : ℝ} (hgap : a / 2 < p - a / 2) :
    InjOn (P.meridianCutFrontierMap a)
      (D ×ˢ ({a / 2, p - a / 2} : Set ℝ)) := by
  intro z hz w hw heq
  have hzt : z.2 = a / 2 ∨ z.2 = p - a / 2 := hz.2
  have hwt : w.2 = a / 2 ∨ w.2 = p - a / 2 := hw.2
  have hzplus : (z.1, (1 / 2 : ℝ)) ∈ D ×ˢ I := ⟨hz.1, by norm_num⟩
  have hzminus : (z.1, -(1 / 2 : ℝ)) ∈ D ×ˢ I := ⟨hz.1, by norm_num⟩
  have hwplus : (w.1, (1 / 2 : ℝ)) ∈ D ×ˢ I := ⟨hw.1, by norm_num⟩
  have hwminus : (w.1, -(1 / 2 : ℝ)) ∈ D ×ˢ I := ⟨hw.1, by norm_num⟩
  rcases hzt with hzt | hzt <;> rcases hwt with hwt | hwt
  · have hz' : z = (z.1, a / 2) := Prod.ext rfl hzt
    have hw' : w = (w.1, a / 2) := Prod.ext rfl hwt
    rw [hz', hw', P.meridianCutFrontierMap_lower,
      P.meridianCutFrontierMap_lower] at heq
    have hpairs := P.injective hzplus hwplus heq
    have hfirst := congrArg Prod.fst hpairs
    exact Prod.ext hfirst (hzt.trans hwt.symm)
  · have hz' : z = (z.1, a / 2) := Prod.ext rfl hzt
    have hw' : w = (w.1, p - a / 2) := Prod.ext rfl hwt
    rw [hz', hw', P.meridianCutFrontierMap_lower,
      P.meridianCutFrontierMap_upper hgap] at heq
    have htime : (1 / 2 : ℝ) = -(1 / 2 : ℝ) :=
      congrArg Prod.snd (P.injective hzplus hwminus heq)
    norm_num at htime
  · have hz' : z = (z.1, p - a / 2) := Prod.ext rfl hzt
    have hw' : w = (w.1, a / 2) := Prod.ext rfl hwt
    rw [hz', hw', P.meridianCutFrontierMap_upper hgap,
      P.meridianCutFrontierMap_lower] at heq
    have htime : -(1 / 2 : ℝ) = (1 / 2 : ℝ) :=
      congrArg Prod.snd (P.injective hzminus hwplus heq)
    norm_num at htime
  · have hz' : z = (z.1, p - a / 2) := Prod.ext rfl hzt
    have hw' : w = (w.1, p - a / 2) := Prod.ext rfl hwt
    rw [hz', hw', P.meridianCutFrontierMap_upper hgap,
      P.meridianCutFrontierMap_upper hgap] at heq
    have hpairs := P.injective hzminus hwminus heq
    have hfirst := congrArg Prod.fst hpairs
    exact Prod.ext hfirst (hzt.trans hwt.symm)



theorem injective_meridianCutFrontierMap (P : OriginalDiskProduct e R j)
    {a : ℝ} (ha : 0 < a) (hgap : a / 2 < p - a / 2)
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t)) :
    InjOn (P.meridianCutFrontierMap a) (cubePrismBoundary (a / 2) (p - a / 2)) := by
  have htime (z : E) (hz : z ∈ cubePrismBoundary (a / 2) (p - a / 2)) :
      z.2 ∈ Icc (a / 2) (p - a / 2) := by
    rcases hz with hlat | hcap
    · exact hlat.2
    · have ht : z.2 = a / 2 ∨ z.2 = p - a / 2 := hcap.2
      rcases ht with ht | ht <;> rw [ht] <;> exact ⟨by linarith, by linarith⟩
  intro z hz w hw heq
  by_cases hzQ : z.1 ∈ Q
  · have hwQ : w.1 ∈ Q := (P.meridianCutFrontierMap_frontier_iff hgap hmark w hw).mp
      (heq ▸ (P.meridianCutFrontierMap_frontier_iff hgap hmark z hz).mpr hzQ)
    rw [P.meridianCutFrontierMap_lateral hgap hmark z hzQ,
      P.meridianCutFrontierMap_lateral hgap hmark w hwQ] at heq
    exact injOn_hamiltonComplementCylinder (by linarith : 0 < a / 2)
      ⟨hzQ, htime z hz⟩ ⟨hwQ, htime w hw⟩ heq
  · have hwQ : w.1 ∉ Q := by
      intro h
      apply hzQ
      exact (P.meridianCutFrontierMap_frontier_iff hgap hmark z hz).mp
        (heq.symm ▸ (P.meridianCutFrontierMap_frontier_iff hgap hmark w hw).mpr h)
    have hzcap : z ∈ D ×ˢ ({a / 2, p - a / 2} : Set ℝ) :=
      hz.elim (fun h => (hzQ h.1).elim) id
    have hwcap : w ∈ D ×ˢ ({a / 2, p - a / 2} : Set ℝ) :=
      hw.elim (fun h => (hwQ h.1).elim) id
    exact injective_on_caps P hgap hzcap hwcap heq

end PoincareConjecture.M76.OriginalDiskProduct
