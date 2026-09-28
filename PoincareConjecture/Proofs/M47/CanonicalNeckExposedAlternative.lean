import PoincareConjecture.Proofs.M47.CanonicalNeckPhysicalBuffer
import PoincareConjecture.Proofs.M47.CanonicalNeckSlabLimit









set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M47



theorem regularSlab_limit_strongNeck_exposed_bottom
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {T c l H : ℝ}
    (N : SurgeryStrongNeck F T F.parameters.epsilon)
    (hl : l < T - (N.neck.scale⁻¹ ^ 2)⁻¹) (hH : T < H)
    (hDomain : Ico l H ⊆ F.time_domain)
    (hTc : T < c) (hJ : Icc T c ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc T c))
    (times : ℕ → Icc T c) (points : ℕ → (F.slice T).carrier)
    (htimes : Tendsto (fun n => (times n).val) atTop (𝓝 T))
    (hpoints : Tendsto points atTop (𝓝 N.neck.center))
    (hbad : ∀ n, ¬ SurgeryCanonicalControl F (times n).val
      ((F.regular_slabs T c hTc hJ hfree).identify (times n) (points n))
      F.parameters.epsilon F.parameters.C) :
    ∃ E : SurgeryFlowCylinder F (F.slice T) T 1
        (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) N.neck.carrier,
      (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
        (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
        ∀ x ∈ N.neck.carrier,
          HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x)) ∧
      (∀ hs x, x ∈ N.neck.carrier → HEq (E.forward 0 hs x) x) ∧
      ∃ hT : T + (-(N.neck.scale⁻¹ ^ 2)⁻¹) / 1 ∈ F.surgery_times,
        ∀ [Nonempty (F.slice (T + (-(N.neck.scale⁻¹ ^ 2)⁻¹) / 1)).carrier],
          ∃ i : Fin (F.event (T + (-(N.neck.scale⁻¹ ^ 2)⁻¹) / 1) hT).cap_count,
            (E.forward (-(N.neck.scale⁻¹ ^ 2)⁻¹)
                ⟨le_rfl, (neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le)⟩ ''
                N.neck.carrier ∩
              ((F.event (T + (-(N.neck.scale⁻¹ ^ 2)⁻¹) / 1) hT).caps i).carrier).Nonempty := by
  rcases exists_strongNeck_buffer_or_cap N hl hH hDomain with hbuffer | hcap
  · obtain ⟨d, b, hd, hb, _hld, _hbH, E, hagree, hbased⟩ := hbuffer
    let U : TopologicalSpace.Opens (F.slice T).carrier := ⟨N.neck.carrier, N.neck.carrier_open⟩
    exact (regularSlab_limit_not_buffered_neck P N U rfl hd hb E hbased hagree
      hTc hJ hfree times points htimes hpoints hbad).elim
  · exact hcap

end PoincareConjecture.Proofs.M47
