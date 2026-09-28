import PoincareConjecture.Proofs.M51.EpochConstruction












set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M51

open M51Numerical


def StagePoint
    (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (C : RepairedCanonicalInductionData S N)
    (F₀ : SurgeryFlowData.{u}) (n : ℕ) :=
  {X : Σ F : SurgeryFlowData.{u}, EpochStage S N C n F //
    X.2.extension.extended.parameters = F₀.parameters ∧
      X.2.observation.H = surgeryEpochStart (n + 2)}


noncomputable def stageNode
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S}
    {C : RepairedCanonicalInductionData S N}
    (A : M48AnalyticCalibration S) (P : M48Predecessors.{u})
    (d : ℝ) (hd : (M51Numerical.schedule S N C).Delta 0 ≤ d)
    (count : ∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
      0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
      ∃ bound : ℕ, ∀ (G : SurgeryFlowData.{u}) (O : SurgeryObservation G),
        G.standard_initial = S.setup.standard_initial →
        G.local_constants = S.constants → O.H ≤ B →
        RepairedObservedVolumeControls G O →
        calibratedMetricVolume (G.metric 0) univ ≤ V₀ →
        (∀ t ∈ G.surgery_times ∩ surgeryObservationInterval O,
          G.parameters.delta t ≤ d ∧ hMin ≤ G.parameters.h t) →
        ∀ A : Finset ℝ,
          (↑A : Set ℝ) ⊆ G.surgery_times ∩ surgeryObservationInterval O →
            A.card ≤ bound)
    (delta : ℝ → ℝ) {F₀ : SurgeryFlowData.{u}}
    (X₀ : EpochStage S N C 0 F₀)
    (hdelta : ∀ t, 0 ≤ t → F₀.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F₀.parameters.r t = (M51Numerical.schedule S N C).r j ∧
      F₀.parameters.kappa t = (M51Numerical.schedule S N C).kappa j ∧
      F₀.parameters.h t = S.setup.selector.h
        (delta t * F₀.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (M51Numerical.schedule S N C).Delta j) :
    ∀ n, StagePoint S N C F₀ n
  | 0 => by
      let Y := Classical.choose (X₀.complete A P d hd count delta hdelta hprofiles hcut)
      have hY := Classical.choose_spec
        (X₀.complete A P d hd count delta hdelta hprofiles hcut)
      exact ⟨⟨F₀, Y⟩, ⟨Y.extension.parameters_eq,
        by simpa only [prefix_index] using hY⟩⟩
  | n + 1 => by
      let previous := stageNode A P d hd count delta X₀ hdelta hprofiles hcut n
      let X := previous.val
      have hparamsX : X.1.parameters = F₀.parameters :=
        X.2.extension.parameters_eq.symm.trans previous.property.1
      have hdeltaX : ∀ t, 0 ≤ t → X.1.parameters.delta t = delta t := by
        intro t ht
        calc
          X.1.parameters.delta t = F₀.parameters.delta t := by rw [hparamsX]
          _ = delta t := hdelta t ht
      have hprofilesX : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
          X.1.parameters.r t = (M51Numerical.schedule S N C).r j ∧
          X.1.parameters.kappa t = (M51Numerical.schedule S N C).kappa j ∧
          X.1.parameters.h t = S.setup.selector.h
            (delta t * X.1.parameters.r t) (delta t) := by
        intro j t ht ht0
        simpa only [hparamsX] using hprofiles j t ht ht0
      have hboundary : X.2.observation.H =
          surgeryEpochStart ((prefixAt S N C n).i + 1) := by
        simpa only [prefix_index] using previous.property.2
      let Y := Classical.choose (X.2.promote hdeltaX hprofilesX hcut hboundary)
      have hpromotion : Y.extension = X.2.extension :=
        (Classical.choose_spec (X.2.promote hdeltaX hprofilesX hcut hboundary)).1
      have hsource : Y.extension.extended = X.2.extension.extended :=
        congrArg (fun E : SurgeryFlowExtension X.1 => E.extended) hpromotion
      let rebased₀ := EpochStage.rebase Y
      let rebased : EpochStage S N C (n + 1) X.2.extension.extended :=
        hsource ▸ rebased₀
      have hparamsR : X.2.extension.extended.parameters = F₀.parameters :=
        X.2.extension.parameters_eq.trans hparamsX
      have hdeltaR : ∀ t, 0 ≤ t →
          X.2.extension.extended.parameters.delta t = delta t := by
        intro t ht
        calc
          X.2.extension.extended.parameters.delta t = F₀.parameters.delta t := by
            rw [hparamsR]
          _ = delta t := hdelta t ht
      have hprofilesR : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
          X.2.extension.extended.parameters.r t = (M51Numerical.schedule S N C).r j ∧
          X.2.extension.extended.parameters.kappa t =
            (M51Numerical.schedule S N C).kappa j ∧
          X.2.extension.extended.parameters.h t = S.setup.selector.h
            (delta t * X.2.extension.extended.parameters.r t) (delta t) := by
        intro j t ht ht0
        simpa only [hparamsR] using hprofiles j t ht ht0
      let Z := Classical.choose
        (rebased.complete A P d hd count delta hdeltaR hprofilesR hcut)
      have hZ := Classical.choose_spec
        (rebased.complete A P d hd count delta hdeltaR hprofilesR hcut)
      exact ⟨⟨X.2.extension.extended, Z⟩,
        ⟨Z.extension.parameters_eq.trans hparamsR,
          by simpa only [prefix_index] using hZ⟩⟩


def OffsetStagePoint
    (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (C : RepairedCanonicalInductionData S N)
    (F₀ : SurgeryFlowData.{u}) (k n : ℕ) :=
  {X : Σ F : SurgeryFlowData.{u}, EpochStage S N C (k + n) F //
    X.2.extension.extended.parameters = F₀.parameters ∧
      X.2.observation.H = surgeryEpochStart (k + n + 2)}


noncomputable def stageNodeFrom
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S}
    {C : RepairedCanonicalInductionData S N}
    (A : M48AnalyticCalibration S) (P : M48Predecessors.{u})
    (d : ℝ) (hd : (M51Numerical.schedule S N C).Delta 0 ≤ d)
    (count : ∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
      0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
      ∃ bound : ℕ, ∀ (G : SurgeryFlowData.{u}) (O : SurgeryObservation G),
        G.standard_initial = S.setup.standard_initial →
        G.local_constants = S.constants → O.H ≤ B →
        RepairedObservedVolumeControls G O →
        calibratedMetricVolume (G.metric 0) univ ≤ V₀ →
        (∀ t ∈ G.surgery_times ∩ surgeryObservationInterval O,
          G.parameters.delta t ≤ d ∧ hMin ≤ G.parameters.h t) →
        ∀ A : Finset ℝ,
          (↑A : Set ℝ) ⊆ G.surgery_times ∩ surgeryObservationInterval O →
            A.card ≤ bound)
    (delta : ℝ → ℝ) {F₀ : SurgeryFlowData.{u}} (k : ℕ)
    (X₀ : EpochStage S N C k F₀)
    (hdelta : ∀ t, 0 ≤ t → F₀.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F₀.parameters.r t = (M51Numerical.schedule S N C).r j ∧
      F₀.parameters.kappa t = (M51Numerical.schedule S N C).kappa j ∧
      F₀.parameters.h t = S.setup.selector.h
        (delta t * F₀.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (M51Numerical.schedule S N C).Delta j) :
    ∀ n, OffsetStagePoint S N C F₀ k n
  | 0 => by
      let Y := Classical.choose (X₀.complete A P d hd count delta hdelta hprofiles hcut)
      have hY := Classical.choose_spec
        (X₀.complete A P d hd count delta hdelta hprofiles hcut)
      exact ⟨⟨F₀, Y⟩, ⟨Y.extension.parameters_eq,
        by simpa only [prefix_index] using hY⟩⟩
  | n + 1 => by
      let previous := stageNodeFrom A P d hd count delta k X₀ hdelta hprofiles hcut n
      let X := previous.val
      have hparamsX : X.1.parameters = F₀.parameters :=
        X.2.extension.parameters_eq.symm.trans previous.property.1
      have hdeltaX : ∀ t, 0 ≤ t → X.1.parameters.delta t = delta t := by
        intro t ht
        calc
          X.1.parameters.delta t = F₀.parameters.delta t := by rw [hparamsX]
          _ = delta t := hdelta t ht
      have hprofilesX : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
          X.1.parameters.r t = (M51Numerical.schedule S N C).r j ∧
          X.1.parameters.kappa t = (M51Numerical.schedule S N C).kappa j ∧
          X.1.parameters.h t = S.setup.selector.h
            (delta t * X.1.parameters.r t) (delta t) := by
        intro j t ht ht0
        simpa only [hparamsX] using hprofiles j t ht ht0
      have hboundary : X.2.observation.H =
          surgeryEpochStart ((prefixAt S N C (k + n)).i + 1) := by
        simpa only [prefix_index] using previous.property.2
      let Y := Classical.choose (X.2.promote hdeltaX hprofilesX hcut hboundary)
      have hpromotion : Y.extension = X.2.extension :=
        (Classical.choose_spec (X.2.promote hdeltaX hprofilesX hcut hboundary)).1
      have hsource : Y.extension.extended = X.2.extension.extended :=
        congrArg (fun E : SurgeryFlowExtension X.1 => E.extended) hpromotion
      let rebased₀ := EpochStage.rebase Y
      let rebased : EpochStage S N C (k + (n + 1)) X.2.extension.extended :=
        hsource ▸ rebased₀
      have hparamsR : X.2.extension.extended.parameters = F₀.parameters :=
        X.2.extension.parameters_eq.trans hparamsX
      have hdeltaR : ∀ t, 0 ≤ t →
          X.2.extension.extended.parameters.delta t = delta t := by
        intro t ht
        calc
          X.2.extension.extended.parameters.delta t = F₀.parameters.delta t := by
            rw [hparamsR]
          _ = delta t := hdelta t ht
      have hprofilesR : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
          X.2.extension.extended.parameters.r t = (M51Numerical.schedule S N C).r j ∧
          X.2.extension.extended.parameters.kappa t =
            (M51Numerical.schedule S N C).kappa j ∧
          X.2.extension.extended.parameters.h t = S.setup.selector.h
            (delta t * X.2.extension.extended.parameters.r t) (delta t) := by
        intro j t ht ht0
        simpa only [hparamsR] using hprofiles j t ht ht0
      let Z := Classical.choose
        (rebased.complete A P d hd count delta hdeltaR hprofilesR hcut)
      have hZ := Classical.choose_spec
        (rebased.complete A P d hd count delta hdeltaR hprofilesR hcut)
      exact ⟨⟨X.2.extension.extended, Z⟩,
        ⟨Z.extension.parameters_eq.trans hparamsR,
          by simpa only [prefix_index] using hZ⟩⟩


theorem exists_stage_sequence_from
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S}
    {C : RepairedCanonicalInductionData S N}
    (A : M48AnalyticCalibration S) (P : M48Predecessors.{u})
    (d : ℝ) (hd : (M51Numerical.schedule S N C).Delta 0 ≤ d)
    (count : ∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
      0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
      ∃ bound : ℕ, ∀ (G : SurgeryFlowData.{u}) (O : SurgeryObservation G),
        G.standard_initial = S.setup.standard_initial →
        G.local_constants = S.constants → O.H ≤ B →
        RepairedObservedVolumeControls G O →
        calibratedMetricVolume (G.metric 0) univ ≤ V₀ →
        (∀ t ∈ G.surgery_times ∩ surgeryObservationInterval O,
          G.parameters.delta t ≤ d ∧ hMin ≤ G.parameters.h t) →
        ∀ A : Finset ℝ,
          (↑A : Set ℝ) ⊆ G.surgery_times ∩ surgeryObservationInterval O →
            A.card ≤ bound)
    (delta : ℝ → ℝ) {F₀ : SurgeryFlowData.{u}} (k : ℕ)
    (X₀ : EpochStage S N C k F₀)
    (hdelta : ∀ t, 0 ≤ t → F₀.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F₀.parameters.r t = (M51Numerical.schedule S N C).r j ∧
      F₀.parameters.kappa t = (M51Numerical.schedule S N C).kappa j ∧
      F₀.parameters.h t = S.setup.selector.h
        (delta t * F₀.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (M51Numerical.schedule S N C).Delta j) :
    ∃ stage : ∀ n : ℕ, Σ F : SurgeryFlowData.{u}, EpochStage S N C (k + n) F,
      (stage 0).1 = F₀ ∧
      ∀ n, (stage (n + 1)).1 = (stage n).2.extension.extended ∧
        (stage n).2.observation.H = surgeryEpochStart (k + n + 2) ∧
        (stage n).2.extension.extended.parameters = F₀.parameters := by
  let nodes := stageNodeFrom A P d hd count delta k X₀ hdelta hprofiles hcut
  refine ⟨fun n => (nodes n).val, ?_, ?_⟩
  · rfl
  · intro n
    have hn := (nodes n).property
    exact ⟨rfl, hn.2, hn.1⟩


structure ComposedExtension
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n)) (n k : ℕ) where

  extension : SurgeryFlowExtension (F n)

  extended_eq : extension.extended = F (n + k)

namespace ComposedExtension


theorem castSource_extended {F G : SurgeryFlowData.{u}} (h : F = G)
    (E : SurgeryFlowExtension F) :
    (h ▸ E : SurgeryFlowExtension G).extended = E.extended := by
  cases h
  rfl


@[simp] theorem refl_identify_apply
    (F : SurgeryFlowData.{u}) {t : ℝ} (ht : t ∈ F.time_domain)
    (x : (F.slice t).carrier) :
    (SurgeryFlowExtension.refl F).identify t ht x = x := by
  rfl


theorem trans_identify_apply
    {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F)
    {D : SurgeryFlowExtension E.extended} {t : ℝ}
    (ht : t ∈ F.time_domain) (x : (F.slice t).carrier) :
    (SurgeryFlowExtension.trans E D).identify t ht x =
      D.identify t (E.old_times ht) (E.identify t ht x) := by
  rfl


theorem trans_assoc_identify_apply
    {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F)
    {D : SurgeryFlowExtension E.extended}
    {G : SurgeryFlowExtension D.extended} {t : ℝ}
    (ht : t ∈ F.time_domain) (x : (F.slice t).carrier) :
    ((SurgeryFlowExtension.trans E D).trans G).identify t ht x =
      (SurgeryFlowExtension.trans E (SurgeryFlowExtension.trans D G)).identify
        t ht x := by
  rfl


noncomputable def append {F G : SurgeryFlowData.{u}}
    (D : SurgeryFlowExtension F) (hD : D.extended = G)
    (E : SurgeryFlowExtension G) : SurgeryFlowExtension F :=
  D.trans (hD.symm ▸ E)


@[simp] theorem append_extended {F G : SurgeryFlowData.{u}}
    (D : SurgeryFlowExtension F) (hD : D.extended = G)
    (E : SurgeryFlowExtension G) : (append D hD E).extended = E.extended := by
  subst G
  rfl


@[simp] theorem append_refl {F G : SurgeryFlowData.{u}}
    (D : SurgeryFlowExtension F) (hD : D.extended = G) :
    append D hD (SurgeryFlowExtension.refl G) = D := by
  subst G
  cases D
  rfl


theorem append_assoc {F G H : SurgeryFlowData.{u}}
    (D : SurgeryFlowExtension F) (hD : D.extended = G)
    (E : SurgeryFlowExtension G) (hE : E.extended = H)
    (Q : SurgeryFlowExtension H) :
    append (append D hD E) ((append_extended D hD E).trans hE) Q =
      append D hD (append E hE Q) := by
  subst G
  subst H
  rfl


noncomputable def identifyTo {F G : SurgeryFlowData.{u}}
    (D : SurgeryFlowExtension F) (hD : D.extended = G)
    (t : ℝ) (ht : t ∈ F.time_domain) :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice t).carrier (G.slice t).carrier ∞ :=
  hD ▸ D.identify t ht


theorem oldTimeTo {F G : SurgeryFlowData.{u}}
    (D : SurgeryFlowExtension F) (hD : D.extended = G)
    {t : ℝ} (ht : t ∈ F.time_domain) : t ∈ G.time_domain :=
  hD ▸ D.old_times ht


theorem identifyTo_append {F G H : SurgeryFlowData.{u}}
    (D : SurgeryFlowExtension F) (hD : D.extended = G)
    (E : SurgeryFlowExtension G) (hE : E.extended = H)
    (t : ℝ) (ht : t ∈ F.time_domain) :
    identifyTo (append D hD E) ((append_extended D hD E).trans hE) t ht =
      (identifyTo D hD t ht).trans (identifyTo E hE t (oldTimeTo D hD ht)) := by
  subst G
  subst H
  rfl


noncomputable def identify {F : ℕ → SurgeryFlowData.{u}}
    {E : ∀ n, SurgeryFlowExtension (F n)} {n k : ℕ}
    (D : ComposedExtension F E n k) (t : ℝ) (ht : t ∈ (F n).time_domain) :
    Diffeomorph (𝓡 3) (𝓡 3) ((F n).slice t).carrier ((F (n + k)).slice t).carrier ∞ :=
  identifyTo D.extension D.extended_eq t ht


theorem old_times {F : ℕ → SurgeryFlowData.{u}}
    {E : ∀ n, SurgeryFlowExtension (F n)} {n k : ℕ}
    (D : ComposedExtension F E n k) {t : ℝ} (ht : t ∈ (F n).time_domain) :
    t ∈ (F (n + k)).time_domain := oldTimeTo D.extension D.extended_eq ht


noncomputable def chain
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n))
    (hE : ∀ n, (E n).extended = F (n + 1))
    (n : ℕ) : ∀ k, ComposedExtension F E n k
  | 0 => ⟨SurgeryFlowExtension.refl (F n), rfl⟩
  | k + 1 => by
      let previous := chain F E hE n k
      exact ⟨append previous.extension previous.extended_eq (E (n + k)),
        (append_extended previous.extension previous.extended_eq (E (n + k))).trans
          (hE (n + k))⟩


theorem chain_add
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n))
    (hE : ∀ n, (E n).extended = F (n + 1)) (n k l : ℕ) :
    (chain F E hE n (k + l)).extension =
      append (chain F E hE n k).extension (chain F E hE n k).extended_eq
        (chain F E hE (n + k) l).extension := by
  induction l with
  | zero => simp only [Nat.add_zero, chain, append_refl]
  | succ l ih =>
    simp only [Nat.add_succ, chain]
    rw [← append_assoc]
    simp only [← ih]
    congr! 2 <;> (change n + (k + l) = n + k + l; omega)


theorem chain_identify_add
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n))
    (hE : ∀ n, (E n).extended = F (n + 1)) (n k l : ℕ)
    (t : ℝ) (ht : t ∈ (F n).time_domain) :
    HEq ((chain F E hE n (k + l)).identify t ht)
      (((chain F E hE n k).identify t ht).trans
        ((chain F E hE (n + k) l).identify t ((chain F E hE n k).old_times ht))) := by
  have h := identifyTo_append (chain F E hE n k).extension
    (chain F E hE n k).extended_eq (chain F E hE (n + k) l).extension
    (chain F E hE (n + k) l).extended_eq t ht
  apply HEq.trans ?_ (heq_of_eq h)
  unfold identify
  congr! 1
  · congr 1
    omega
  · exact chain_add F E hE n k l


noncomputable def between
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n))
    (hE : ∀ n, (E n).extended = F (n + 1)) (n m : ℕ) (_h : n ≤ m) :
    SurgeryFlowExtension (F n) := (chain F E hE n (m - n)).extension


theorem between_extended
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n))
    (hE : ∀ n, (E n).extended = F (n + 1)) (n m : ℕ) (h : n ≤ m) :
    (between F E hE n m h).extended = F m :=
  (chain F E hE n (m - n)).extended_eq.trans (congrArg F (Nat.add_sub_of_le h))


@[simp] theorem between_self
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n))
    (hE : ∀ n, (E n).extended = F (n + 1)) (n : ℕ) :
    between F E hE n n le_rfl = SurgeryFlowExtension.refl (F n) := by
  unfold between
  rw [Nat.sub_self]
  rfl


theorem between_trans
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n))
    (hE : ∀ n, (E n).extended = F (n + 1)) (n m k : ℕ)
    (hnm : n ≤ m) (hmk : m ≤ k) :
    between F E hE n k (hnm.trans hmk) =
      append (between F E hE n m hnm) (between_extended F E hE n m hnm)
        (between F E hE m k hmk) := by
  change (chain F E hE n (k - n)).extension =
    append (chain F E hE n (m - n)).extension
      ((chain F E hE n (m - n)).extended_eq.trans (congrArg F (Nat.add_sub_of_le hnm)))
      (chain F E hE m (k - m)).extension
  have hlen : k - n = (m - n) + (k - m) := by omega
  rw [hlen, chain_add]
  congr! 3
  omega


noncomputable def identifyBetween
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n))
    (hE : ∀ n, (E n).extended = F (n + 1)) (n m : ℕ) (hnm : n ≤ m)
    (t : ℝ) (ht : t ∈ (F n).time_domain) :
    Diffeomorph (𝓡 3) (𝓡 3) ((F n).slice t).carrier ((F m).slice t).carrier ∞ :=
  identifyTo (between F E hE n m hnm) (between_extended F E hE n m hnm) t ht


theorem oldTimeBetween
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n))
    (hE : ∀ n, (E n).extended = F (n + 1)) (n m : ℕ) (hnm : n ≤ m)
    {t : ℝ} (ht : t ∈ (F n).time_domain) : t ∈ (F m).time_domain :=
  oldTimeTo (between F E hE n m hnm) (between_extended F E hE n m hnm) ht


theorem identifyBetween_trans
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n))
    (hE : ∀ n, (E n).extended = F (n + 1)) (n m k : ℕ)
    (hnm : n ≤ m) (hmk : m ≤ k) (t : ℝ) (ht : t ∈ (F n).time_domain) :
    identifyBetween F E hE n k (hnm.trans hmk) t ht =
      (identifyBetween F E hE n m hnm t ht).trans
        (identifyBetween F E hE m k hmk t (oldTimeBetween F E hE n m hnm ht)) := by
  have h := identifyTo_append (between F E hE n m hnm)
    (between_extended F E hE n m hnm) (between F E hE m k hmk)
    (between_extended F E hE m k hmk) t ht
  simpa only [identifyBetween, oldTimeBetween,
    ← between_trans F E hE n m k hnm hmk] using h


theorem exists_of_le
    (F : ℕ → SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (F n))
    (hE : ∀ n, (E n).extended = F (n + 1))
    (n m : ℕ) (h : n ≤ m) :
    ∃ D : SurgeryFlowExtension (F n), D.extended = F m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨(chain F E hE n k).extension, (chain F E hE n k).extended_eq⟩

end ComposedExtension


theorem exists_stage_sequence
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S}
    {C : RepairedCanonicalInductionData S N}
    (A : M48AnalyticCalibration S) (P : M48Predecessors.{u})
    (d : ℝ) (hd : (M51Numerical.schedule S N C).Delta 0 ≤ d)
    (count : ∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
      0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
      ∃ bound : ℕ, ∀ (G : SurgeryFlowData.{u}) (O : SurgeryObservation G),
        G.standard_initial = S.setup.standard_initial →
        G.local_constants = S.constants → O.H ≤ B →
        RepairedObservedVolumeControls G O →
        calibratedMetricVolume (G.metric 0) univ ≤ V₀ →
        (∀ t ∈ G.surgery_times ∩ surgeryObservationInterval O,
          G.parameters.delta t ≤ d ∧ hMin ≤ G.parameters.h t) →
        ∀ A : Finset ℝ,
          (↑A : Set ℝ) ⊆ G.surgery_times ∩ surgeryObservationInterval O →
            A.card ≤ bound)
    (delta : ℝ → ℝ) {F₀ : SurgeryFlowData.{u}}
    (X₀ : EpochStage S N C 0 F₀)
    (hdelta : ∀ t, 0 ≤ t → F₀.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F₀.parameters.r t = (M51Numerical.schedule S N C).r j ∧
      F₀.parameters.kappa t = (M51Numerical.schedule S N C).kappa j ∧
      F₀.parameters.h t = S.setup.selector.h
        (delta t * F₀.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (M51Numerical.schedule S N C).Delta j) :
    ∃ stage : ∀ n : ℕ, Σ F : SurgeryFlowData.{u}, EpochStage S N C n F,
      (stage 0).1 = F₀ ∧
      ∀ n, (stage (n + 1)).1 = (stage n).2.extension.extended ∧
        (stage n).2.observation.H = surgeryEpochStart (n + 2) ∧
        (stage n).2.extension.extended.parameters = F₀.parameters := by
  let nodes := stageNode A P d hd count delta X₀ hdelta hprofiles hcut
  refine ⟨fun n => (nodes n).val, ?_, ?_⟩
  · rfl
  · intro n
    have hn := (nodes n).property
    exact ⟨rfl, hn.2, hn.1⟩

end PoincareConjecture.M51
