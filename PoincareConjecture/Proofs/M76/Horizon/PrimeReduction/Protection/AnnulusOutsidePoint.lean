import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.OriginalSphereSimplyConnected
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusHomeomorph
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PeriodCircleLoop
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereAnnulusDisks








set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

theorem not_simplyConnected_squareAnnulus {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) :
    ¬ SimplyConnectedSpace (squareAnnulus L d) := by
  intro h
  let := h
  have hL : 0 < L := by linarith
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  obtain ⟨H, _⟩ := exists_annulus_homeomorph hL hd.le hwidth
  let z : Icc (-d) d := ⟨0, by constructor <;> linarith⟩
  let s : C(AddCircle (4 * L), squareAnnulus L d) :=
    ⟨fun x => H (x, z), H.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let r : C(squareAnnulus L d, AddCircle (4 * L)) :=
    ⟨fun x => (H.symm x).1, continuous_fst.comp H.symm.continuous⟩
  have hcomp : r.comp s = ContinuousMap.id (AddCircle (4 * L)) := by
    ext x
    exact congrArg Prod.fst (H.symm_apply_apply (x, z))
  let gamma := (AddCircle.periodLoop (4 * L)).map s.continuous
  have hnull := ((simply_connected_iff_loops_nullhomotopic.mp h).2 (s 0) gamma).map r
  change (((AddCircle.periodLoop (4 * L)).map s.continuous).map r.continuous).Homotopic
    (Path.refl (r (s 0))) at hnull
  rw [Path.map_map] at hnull
  change ((AddCircle.periodLoop (4 * L)).map (r.comp s).continuous).Homotopic
    (Path.refl ((r.comp s) 0)) at hnull
  rw [hcomp] at hnull
  exact AddCircle.periodLoop_not_homotopic_refl (4 * L) (by simpa using hnull)

theorem ChartwisePLSphere.exists_point_outside_annulus
    {X α : Type*} [TopologicalSpace X]
    {e : α → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S A : Set X}
    (s : ChartwisePLSphere e S) {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (H : squareAnnulus L d ≃ₜ A) (hAS : A ⊆ S) :
    (S \ A).Nonempty := by
  by_contra hnot
  have heq : A = S := Subset.antisymm hAS (by
    intro x hx
    by_contra hn
    exact hnot ⟨x, hx, hn⟩)
  let : SimplyConnectedSpace S := s.simplyConnectedSpace
  exact not_simplyConnected_squareAnnulus hd hwidth
    ((H.trans (Homeomorph.setCongr heq)).toHomotopyEquiv.simplyConnectedSpace)

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Ann" => squareAnnulus 8 1




theorem ChartwisePLSphere.exists_marked_annulus_complement_disks
    {X α : Type*} [TopologicalSpace X]
    {e : α → OpenPartialHomeomorph X V3} {S A : Set X}
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (H : Ann ≃ₜ A) (hAS : A ⊆ S)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f Ann)
    (hHval : ∀ z : Ann, (H z : X) = f z) :
    ∃ k q : Bool → Set V3,
      (∀ i, IsFinitePLBallPair P2 (k i) (q i) ∧ k i ⊆ Sphere ∧
        (s.map '' k i) ∩ A = s.map '' q i ∧
        s.map '' q i = (fun z : Ann => (H z : X)) ''
          {z | depth 8 z = if i then 1 else -1}) ∧
      Disjoint (s.map '' k true) (s.map '' k false) ∧
      ((s.map '' k true) ∪ (s.map '' k false)) ∪ A = S := by
  obtain ⟨p, hpS, hpA⟩ := s.exists_point_outside_annulus (by norm_num) (by norm_num) H hAS
  have hfi : InjOn f Ann := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hHval ⟨x, hx⟩).trans (hxy.trans (hHval ⟨y, hy⟩).symm))))
  have himage : f '' Ann = A := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      rw [← hHval ⟨z, hz⟩]
      exact (H ⟨z, hz⟩).property
    · intro x hx
      obtain ⟨z, hz⟩ := H.surjective ⟨x, hx⟩
      exact ⟨z, z.property, (hHval z).symm.trans (congrArg Subtype.val hz)⟩
  have hfS : MapsTo f Ann S := fun z hz => hAS (himage.subset ⟨z, hz, rfl⟩)
  obtain ⟨g, k, q, C, hg, hgS, hvalue, hgimage, hk, hdis, hcover, hprod⟩ :=
    s.exists_original_annulus_disks hcompat f hf hfi hfS ⟨p, hpS⟩ (himage.symm ▸ hpA)
  refine ⟨k, q, ?_, hdis, himage ▸ hcover⟩
  intro i
  refine ⟨(hk i).1, (hk i).2.1, himage ▸ (hk i).2.2.2.2, ?_⟩
  rw [(hk i).2.2.2.1]
  apply image_congr
  intro z _
  exact (hHval z).symm

end PoincareConjecture.M76
