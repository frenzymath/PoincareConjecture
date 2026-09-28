import PoincareConjecture.Proofs.M51.EmptyRegularSlab









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Empty

variable (F : SurgeryFlowData.{u}) {a : ℝ} (ha : a ∈ F.time_domain)
    [IsEmpty (F.slice a).carrier]

noncomputable def identify (t : ℝ) (ht : t ∈ F.time_domain) :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice t).carrier (slice F a t).carrier ∞ := by
  classical
  by_cases hta : t ≤ a
  · exact M51EventCopy.identify F.slice (fun s => min s a) t (min_eq_left hta)
  · letI := F.extinction_permanent a t ha ht (lt_of_not_ge hta).le inferInstance
    letI := empty_after F a (lt_of_not_ge hta).le
    exact Diffeomorph.empty

theorem identify_of_le (t : ℝ) (ht : t ∈ F.time_domain) (hta : t ≤ a) :
    identify F ha t ht =
      M51EventCopy.identify F.slice (fun s => min s a) t (min_eq_left hta) := by
  unfold identify
  exact dif_pos hta

theorem identify_heq (t : ℝ) (ht : t ∈ F.time_domain) (x : (F.slice t).carrier) :
    HEq (identify F ha t ht x) x := by
  classical
  by_cases hta : t ≤ a
  · simpa only [identify, dif_pos hta, slice] using
      M51EventCopy.identify_apply_heq F.slice (fun s => min s a) t (min_eq_left hta) x
  · let := F.extinction_permanent a t ha ht (lt_of_not_ge hta).le inferInstance
    exact isEmptyElim x

theorem identify_metric_pullback (t : ℝ) (ht : t ∈ F.time_domain)
    (x : (F.slice t).carrier) (v w : TangentSpace (𝓡 3) x) :
    (metric F a t).inner (identify F ha t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (identify F ha t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identify F ha t ht) x w) =
        (F.metric t).inner x v w := by
  classical
  by_cases hta : t ≤ a
  · rw [identify_of_le F ha t ht hta]
    exact M51EventCopy.identify_metric_pullback F.slice F.metric
      (fun s => min s a) t (min_eq_left hta) x v w
  · let := F.extinction_permanent a t ha ht (lt_of_not_ge hta).le inferInstance
    exact isEmptyElim x

theorem identify_ordinary_compatibility (p q : ℝ) (hpq : p < q)
    (hJ : Icc p q ⊆ F.time_domain) (hfree : Disjoint F.surgery_times (Ioc p q))
    (hJ' : Icc p q ⊆ Ici 0) (s t : Icc p q) (x : (F.slice s.1).carrier) :
    (regularSlab F ha p q hpq hJ' hfree).transport s t (identify F ha s.1 (hJ s.2) x) =
      identify F ha t.1 (hJ t.2)
        ((F.regular_slabs p q hpq hJ hfree).transport s t x) := by
  have hqa := regularSlab_end_le F ha p q hpq hJ' hfree s.2
    (identify F ha s.1 (hJ s.2) x)
  have hleft := regularSlab_transport_heq F ha p q hpq hJ' hfree hqa hJ s t
    (identify_heq F ha s.1 (hJ s.2) x)
  exact eq_of_heq (hleft.trans (identify_heq F ha t.1 (hJ t.2) _).symm)

end PoincareConjecture.M51Empty
