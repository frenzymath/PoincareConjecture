import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCuts
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem CapCertificate.inter_subset_end_region_of_avoids_slice
    (C : CapCertificate g) {t : ℝ}
    (ht : t ∈ Set.Ioo (-C.epsilon⁻¹) C.epsilon⁻¹)
    {Y : Set M} (hY : IsPreconnected Y)
    (havoid : Disjoint Y
      (C.end_neck.coordinate_map '' (Set.univ ×ˢ ({t} : Set ℝ))))
    (hout : (Y \ C.carrier).Nonempty) :
    C.carrier ∩ Y ⊆ C.end_neck.region t C.epsilon⁻¹ := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let K := C.carrier \ C.end_neck.region t C.epsilon⁻¹
  have hK : IsClosed K := (C.isCompact_end_neck_lower_cut ht).isClosed
  have hfront : frontier K =
      C.end_neck.coordinate_map '' (univ ×ˢ ({t} : Set ℝ)) :=
    (C.end_neck_lower_cut_topology ht).2.2.2.2.2.1
  have hcover : Y ⊆ interior K ∪ Kᶜ := by
    intro x hx
    by_cases hxi : x ∈ interior K
    · exact Or.inl hxi
    · refine Or.inr fun hxK => ?_
      apply disjoint_left.mp havoid hx
      rw [← hfront]
      exact ⟨subset_closure hxK, hxi⟩
  have houtside : Y ⊆ Kᶜ := by
    rcases hY.subset_or_subset isOpen_interior hK.isOpen_compl
        (disjoint_left.mpr (fun _ hx hy => hy (interior_subset hx))) hcover with h | h
    · obtain ⟨x, hxY, hxC⟩ := hout
      exact False.elim (hxC (interior_subset (h hxY)).1)
    · exact h
  intro x hx
  by_contra hnot
  exact houtside hx.2 ⟨hx.1, hnot⟩

theorem CapCertificate.inter_chain_union_eq_end_neck
    (C : CapCertificate g) (D : BalancedNeckChain g C.epsilon)
    {a : ℤ} (ha : a ∈ D.shape.active)
    (hfirst : ∀ i ∈ D.shape.active, a ≤ i)
    (hstart : D.neck a = C.end_neck)
    (hout : ∀ i ∈ D.shape.active, a < i →
      (D.neck i).center ∉ C.carrier) :
    C.carrier ∩ (⋃ i ∈ D.shape.active, (D.neck i).carrier) =
      C.end_neck.carrier := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  have hL : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  apply Subset.antisymm
  · rintro x ⟨hxC, hxU⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
    by_cases hia : i = a
    · simpa only [hia, hstart] using hxi
    · have hai : a < i := lt_of_le_of_ne (hfirst i hi) (Ne.symm hia)
      obtain ⟨s, hs, hdisj⟩ := D.later_disjoint_negative_end a ha i hi hai
      rw [hstart] at hdisj
      let t := (-C.epsilon⁻¹ + s) / 2
      have ht : t ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := by
        dsimp only [t]
        constructor <;> linarith [hs.1, hs.2]
      have hts : t < s := by dsimp only [t]; linarith [hs.1]
      have htN : t ∈ Ioo (-C.end_neck.epsilon⁻¹) C.end_neck.epsilon⁻¹ := by
        rw [C.end_neck_epsilon]
        exact ht
      have hslice : C.end_neck.coordinate_map '' (univ ×ˢ ({t} : Set ℝ)) ⊆
          C.end_neck.region (-C.epsilon⁻¹) s := by
        rintro y ⟨⟨q, r⟩, ⟨_, hr⟩, rfl⟩
        have hrt : r = t := hr
        subst r
        refine ⟨C.end_neck.coordinate_map_mem ⟨mem_univ _, htN⟩, ?_⟩
        rw [C.end_neck.coordinate_inverse_map (q, t) htN]
        exact ⟨ht.1, hts⟩
      have hbarrier := C.inter_subset_end_region_of_avoids_slice ht
        (D.neck i).isConnected_carrier.isPreconnected (hdisj.mono_right hslice)
        ⟨(D.neck i).center,
          (D.neck i).central_sphere_subset (D.neck i).center_on_central_sphere,
          hout i hi hai⟩
      exact (hbarrier ⟨hxC, hxi⟩).1
  · intro x hx
    refine ⟨C.end_neck_subset hx, mem_iUnion₂.mpr ⟨a, ha, ?_⟩⟩
    simpa only [hstart] using hx

end PoincareConjecture
