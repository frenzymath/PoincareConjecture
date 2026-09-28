import PoincareConjecture.Proofs.M30.Generalized.BoxCylinder
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transitions











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M30



theorem box_forward_mfderiv_bijective (F : GeneralizedRicciFlowData.{u})
    (b : F.box_index) (t : ℝ) (ht : t ∈ (F.box b).interval)
    (x : (F.box b).carrier.carrier) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) ((F.box b).forward t ht) x) :=
  ((F.box b).flow.metric t).mfderiv_bijective_of_pullback_eq (F.metric t) x
    ((F.box b).metric_pullback t ht x)



theorem box_inverse_regular (F : GeneralizedRicciFlowData.{u})
    (b : F.box_index) (t : ℝ) (ht : t ∈ (F.box b).interval)
    (x : (F.slice t).carrier) (hx : x ∈ range ((F.box b).forward t ht)) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ ((F.box b).inverse t ht) x ∧
      Function.Bijective (mfderiv (𝓡 3) (𝓡 3) ((F.box b).inverse t ht) x) := by
  have hi := ((F.box b).inverse_smooth t ht).contMDiffAt
    (((F.box b).forward_openEmbedding t ht).isOpen_range.mem_nhds hx)
  refine ⟨hi, ?_⟩
  obtain ⟨y, rfl⟩ := hx
  have hf := ((F.box b).forward_smooth t ht).contMDiffAt (x := y)
  have heq : (F.box b).inverse t ht ∘ (F.box b).forward t ht = id :=
    funext ((F.box b).left_inverse t ht)
  have hcomp := mfderiv_comp y (hi.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  rw [heq, mfderiv_id] at hcomp
  apply (Function.Bijective.of_comp_iff _ (box_forward_mfderiv_bijective F b t ht y)).mp
  change Function.Bijective
    ((mfderiv (𝓡 3) (𝓡 3) ((F.box b).inverse t ht)
      ((F.box b).forward t ht y)).comp
        (mfderiv (𝓡 3) (𝓡 3) ((F.box b).forward t ht) y))
  rw [← hcomp]
  exact Function.bijective_id

namespace Cylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ}
  {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {p : M → C.carrier}



theorem regularAt_of_meeting_box
    (e : ∀ a : M, GeneralizedFlowCylinder F C origin scale I {p a})
    (hI : I.OrdConnected) {a : M} {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I)
    (b : F.box_index) (hbs : origin + s / scale ∈ (F.box b).interval)
    (hbt : origin + t / scale ∈ (F.box b).interval)
    (ha : (e a).forward s hs (p a) ∈ range ((F.box b).forward _ hbs))
    (hreg : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun z => (e z).forward s hs (p z)) a ∧
      Function.Bijective
        (mfderiv (𝓡 3) (𝓡 3) (fun z => (e z).forward s hs (p z)) a)) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun z => (e z).forward t ht (p z)) a ∧
      Function.Bijective
        (mfderiv (𝓡 3) (𝓡 3) (fun z => (e z).forward t ht (p z)) a) := by
  let fs := fun z : M => (e z).forward s hs (p z)
  let ft := fun z : M => (e z).forward t ht (p z)
  let ib := (F.box b).inverse (origin + s / scale) hbs
  let fb := (F.box b).forward (origin + t / scale) hbt
  have hnear : ∀ᶠ z in 𝓝 a, fs z ∈ range ((F.box b).forward _ hbs) :=
    hreg.1.continuousAt.preimage_mem_nhds
      (((F.box b).forward_openEmbedding _ hbs).isOpen_range.mem_nhds ha)
  have heq : ft =ᶠ[𝓝 a] fb ∘ (ib ∘ fs) := by
    filter_upwards [hnear] with z hz
    exact forward_eq_box_on_overlap (e z) hI (mem_singleton (p z)) b (ib (fs z))
      hs hbs (((F.box b).right_inverse _ hbs hz).symm) t ht hbt
  have hi := box_inverse_regular F b _ hbs (fs a) ha
  have hinner : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (ib ∘ fs) a := hi.1.comp a hreg.1
  have houter : ContMDiffAt (𝓡 3) (𝓡 3) ∞ fb (ib (fs a)) :=
    ((F.box b).forward_smooth _ hbt).contMDiffAt
  have hinner_bij : Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (ib ∘ fs) a) := by
    rw [mfderiv_comp a (hi.1.mdifferentiableAt (by simp))
      (hreg.1.mdifferentiableAt (by simp))]
    exact hi.2.comp hreg.2
  refine ⟨(houter.comp a hinner).congr_of_eventuallyEq heq, ?_⟩
  change Function.Bijective (mfderiv (𝓡 3) (𝓡 3) ft a)
  rw [heq.mfderiv_eq, mfderiv_comp a (houter.mdifferentiableAt (by simp))
    (hinner.mdifferentiableAt (by simp))]
  exact (box_forward_mfderiv_bijective F b _ hbt _).comp hinner_bij




theorem regularAt_of_initial
    (e : ∀ a : M, GeneralizedFlowCylinder F C origin scale I {p a})
    (hI : I.OrdConnected) (a : M) {s₀ : ℝ} (hs₀ : s₀ ∈ I)
    (hinit : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun z => (e z).forward s₀ hs₀ (p z)) a ∧
      Function.Bijective
        (mfderiv (𝓡 3) (𝓡 3) (fun z => (e z).forward s₀ hs₀ (p z)) a)) :
    ∀ t (ht : t ∈ I),
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun z => (e z).forward t ht (p z)) a ∧
        Function.Bijective
          (mfderiv (𝓡 3) (𝓡 3) (fun z => (e z).forward t ht (p z)) a) := by
  let P : I → Prop := fun t =>
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun z => (e z).forward t.1 t.2 (p z)) a ∧
      Function.Bijective
        (mfderiv (𝓡 3) (𝓡 3) (fun z => (e z).forward t.1 t.2 (p z)) a)
  have hlocal (s : I) : ∀ᶠ t in 𝓝 s, (P s ↔ P t) ∧ (P t ↔ P s) := by
    obtain ⟨b, y, delta, hdelta, hb⟩ :=
      (e a).vertical_compatibility s.1 s.2 (p a) (mem_singleton (p a))
    obtain ⟨hbs, hse⟩ := hb s.1 s.2 (by simpa using hdelta)
    have hnear : {t : I | |t.1 - s.1| < delta} ∈ 𝓝 s := by
      apply (isOpen_lt (continuous_subtype_val.sub continuous_const).abs
        continuous_const).mem_nhds
      simpa using hdelta
    filter_upwards [hnear] with t ht
    obtain ⟨hbt, hte⟩ := hb t.1 t.2 ht
    have hequiv : P s ↔ P t :=
      ⟨fun hs => regularAt_of_meeting_box e hI s.2 t.2 b hbs hbt ⟨y, hse.symm⟩ hs,
       fun ht => regularAt_of_meeting_box e hI t.2 s.2 b hbt hbs ⟨y, hte.symm⟩ ht⟩
    exact ⟨hequiv, hequiv.symm⟩
  let : PreconnectedSpace I := Subtype.preconnectedSpace hI.isPreconnected
  intro t ht
  exact (PreconnectedSpace.induction₂' (fun s t => P s ↔ P t) hlocal
    ⟨fun _ _ _ hs ht => hs.trans ht⟩ (⟨s₀, hs₀⟩ : I) ⟨t, ht⟩).mp hinit

end Cylinder

end PoincareConjecture.M30
