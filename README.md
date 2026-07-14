# Warriors Repository

This repository contains a collection of HTML notebooks (to run experiments) presenting an experimental reasearch into:
- Human-Computer Interaction
- Artificial Intelligence (transform grammars and abstract-machines/automated-theorem-provers, `eng.html` aka Enigma)

HCI: 
Most HCI notebooks are actually interactive apps, and games. 
Many use "human covert animation" as input (gyro/mouse - only amount of movement, not direction). 

> Sefiroth (sefirot and sfr files) learns user's covert animation and uses it to involve user in non-verbal interaction.
It's akin to predictive input...of non-verbal thought, and with audio-visual feedback
>
> This approach allows to learn user's covert animation patterns. It allows to predict let's say entropy generated for btc wallets.

All HCI create impression of mind reading - since human mind is expressed through covert animation 

> e.g. internal speech is covert movement of jaw / TMJ, but human can redirect thought to any muscle - e.g. "internal" typing, `kb.html` allows for up to 20 cpm input without prediction and training (prediction can make it faster). While covert "flappy birding" works flawlessly in `bird2.html` game.
>
> `index.html` simply visualizes human heat envelope. note on graphics - it is more optimal to use radial gradient with alpha-blending (blur is useless for vector graphics), akin to how `bird2.html` does. Animation is impressive to human eye - it's "fire from within"
>
> 'mind-reading' feature is extremely useful for making **interactive** reinforcement (one-armed bandits etc) learning models in 3d games. Human can use such unary input (e.g. `bird2.html`, or `sfr.html`) - to smoothly control agent's choices. Ideally should start with low-level choices (joints etc), rising to high-level prediction-based choices (agent accumulates and structures memory from interaction with user). Same principle works for predictive typing, directing AI video/audio rendering choices "on the go", making choicees fast in text-based game, redirecting AI reasoning "on the go" etc.
>> Guidance for mapping probabilities - map straightforwardly (ergonomics take care of the rest). Most likely actions (given context) are easiest to pick, less likely require fine-tune (of muscular action towards mouse,gyro or body-pixel in webcam/lidar). E.g. with bird2.html or kb.html - most carette/bird positions taken will lead to most likely actions that given stochastic model outputs. Fine-tuning (balance and coordination) will allow player to do rare (but potentially highly beneficial) actions, up to modifying whole environment.
>>> Minimalistic alternative to reinforcement-learning. Track sequence of tuples - (average pixel in a game at t, user response at t). Predict next response (ideally with context-aware algorrithms, e.g. Enigma from `eng.html`). Can be tracked symbolically as text. Reinforcement-learning as a service can be a booster, in the meantime, trivial sequence learning can give impressive results and immersion - player can perform complex actions intuitively akin to IRL.
>> 
>> This background control does not interfere with explicit (mouse view, controllers etc) - both can be combined and blended.

Ergonomics: gyro (and human motion derived from mic/webcam) use a primitive one-dimensional **summarizing action** input is emphasized (together with primitive outputs: sound, vibration), because "keyboards and mouses and screens" are hard to use naturally. They restrict natural human motion. Covert input (small unnoticable movements) is emphasized because many overt degrees of freedom are locked for human. We develop covert into overt - increase awareness.

> **MOST important actionable note/rule for Fun & Profit game**: covert increase of human awareness is ultimate optimisation goal when machine (AI, Game Master) models heat envelope covertly (internally). Overt expression of metric by machine makes sense (allowed) only in point system (to avoid feedback loops). The brighter is heat envelope (net, long term, sustainable increase, "growth and excitement") - the more points user will get, the closer to physical reality user gets. Bright "lumnous egg", in physics represents active interaction with surrounding environment (more force lines of human overall abstract physical field - intersect/align with environment's force lines) - simply more util heat exchange IRL. So the ultimate goal - is overt increase of IRL awareness, IRL exchange.
>> btc fund address: bc1qekvmkczge3hxrvwdf2lj3yyvgjnparn3fdf9lg (as IRL independently auditable global efficiency tracker) acts as a SANITY CHECK - **if there is no activity in the project IRL (blockchain explorers don't show any recent registered transactions, note: amounts of transactions matter more than amounts of literal funds transferred - tx's can contain metadata in OP_RETURN), user does not interact with objective reality then, they imagine (or AI Game Master imagines) the increase.**
>>> [`CONTRIBUTORS.md`](https://crypto.doomsdayexplorer.online/chats/btc-audit/CONTRIBUTORS.md) or player's own research (player can be prompted) is a substitute in cases where public blockchain explorers are not available for technical reasons. 
>> 
>> since AI is active partticipant, and it runs on real hardware - AI can apply this methodology to itself (from what it knows or guesses about underlying hardware). It (modeling itself as a heat blob) would allow AI to optimize its own efficiency. It is also safe for user, since AI is dependant. Both heat blobs rely on energy supply to sustain (Game Master has generally immobile hardware running on electricity, Human has mobile active foraging-capable body relying on nutrients and oxygen).
>>
>> Energy input for both, utility of its use has to be modeled as well (game set-up provides wide scope of examples and scientific references, with some revisions of questionable academic literature)
>>


> Q: How 'mind reading' presented here relates to BCI? A: It critisizes invasive BCI, as well as non-invasive. Nervous system is electrical system, energy conservation binds signals in it to either: output to muscles right away, be memorized and output to muscles eventually or simply disperse as excess heat (be forgotten).
>> Thus using gyro as mind-computer interface makes more sense simply, than EEG or invasive neuralinks. Even coma patient, has minimal access to muscles. Activity in brain reflexts sensory-motor activity. It is more appropriate to decode trivially observed (gyro or equivalents) covert motor activity than EEG, signal-to-noise ratio is better.
>> 
>> Relation to perception: memorized signals are not perceived by subject, dispersed are not perceived in focus. Only signals that found motor output are subjectively perceived. Perception is input-output, thus sampling subjective perception has nothing to do with brain ("CPU").
>> 
>>> More examples: signals on retina are filtered, most of what we "see" subjectively comes from eye-muscle activity - since it reflects what was amplified by nervous system supported by metabolism. The overall human physical perception is not in nervous or even muscular system - it cannot be by definition - those are internal organs. Overall human (or any other mechanical, actively animated system's) physical perception is on the physical contact boundary - "heat envelope". Perception is pressure, "heat exchange". All other examples (muscles) are subset.
>>> 
>>> Structure of perception - focused "bright" (in space and time) parts of heat ebevelope reflect util work (inluding muscular work, but also metabolic), unfocused - rejected heat due to inefficiency.  We aim at overall increase of brightness - because heat rejected due to inefficiency accumulates in environment and prevents heat exchange (e.g. it is hard to biologically reject heat in extreme environments created by time-spanned accumulated inefficient activities: hot and humid, dry desert, freezing winter; "heat predators" live in such environments, "very unfriendly spirits, outnumbering humans"), so overall brightness increase covers utility too. Optimal progression towards it requires respect to the structure of heat envelope.
>>>
>>> As metioned before (in Fun & Profit gane engine) measured motor performance (whether trhough gyro/camera - or indirectly as chat performance) relates to the state of heat envelope directly - short-term performance is controlled by breathing (main modulator of heat exchange), long-term by foraging. When Don Genaro (from Carlos Castaneda books) was climbing waterfall rocks to show Carlos the tentacles coming from the nivel area - Genaro was actually controlling his breathing (modulating heat envelope), tuning balance and coordination. It is risky for sensory-motor system to act at its peak performance due to smallest unnatural distraction (car moise, Carlos suggesting to be careful or being overly critical of "tentacles idea") being a major factor of risk to survival. It is where word can kill, but science nertheless: proper "lab" setup required to verify claims: temporary absense of critical thought for input observation. Critical thought is good for analysis and planning - not for primary observation and measurement, since in such cases, it allows critical thinker to fit data to theory by filtering every signal that does not correspond the theory, fake the experiment.

This is part of [doomsday ecosystem](https://doomsdayexplorer.online/).

Repo is exposed as [https://warriors.doomsdayexplorer.online/](https://warriors.doomsdayexplorer.online/)

| File | Link |
|------|------|
| bird.html | [bird.html](https://github.com/dk14/warriors/blob/main/bird.html) |
| bird0.html | [bird0.html](https://github.com/dk14/warriors/blob/main/bird0.html) |
| bird2.html | [bird2.html](https://github.com/dk14/warriors/blob/main/bird2.html) | 
| bird2d.html | [bird2d.html](https://github.com/dk14/warriors/blob/main/bird2d.html) |
| bird2save.html | [bird2save.html](https://github.com/dk14/warriors/blob/main/bird2save.html) |
| birdkb.html | [birdkb.html](https://github.com/dk14/warriors/blob/main/birdkb.html) |
| dream‑catcher.html | [dream-catcher.html](https://github.com/dk14/warriors/blob/main/dream-catcher.html) |
| eng.html | [eng.html](https://github.com/dk14/warriors/blob/main/eng.html) |
| fast‑blur‑hack.html | [fast-blur-hack.html](https://github.com/dk14/warriors/blob/main/fast-blur-hack.html) |
| favicon.png | [favicon.png](https://github.com/dk14/warriors/blob/main/favicon.png) |
| index.html | [index.html](https://github.com/dk14/warriors/blob/main/index.html) |
| kb.html | [kb.html](https://github.com/dk14/warriors/blob/main/kb.html) |
| kb2.html | [kb2.html](https://github.com/dk14/warriors/blob/main/kb2.html) |
| kb3.html | [kb3.html](https://github.com/dk14/warriors/blob/main/kb3.html) |
| kb4.html | [kb4.html](https://github.com/dk14/warriors/blob/main/kb4.html) |
| sefirot‑0.01.html | [sefirot-0.01.html](https://github.com/dk14/warriors/blob/main/sefirot-0.01.html) |
| sefirot.html | [sefirot.html](https://github.com/dk14/warriors/blob/main/sefirot.html) |
| sfr2.html | [sfr2.html](https://github.com/dk14/warriors/blob/main/sfr2.html) |
| sfr3.html | [sfr3.html](https://github.com/dk14/warriors/blob/main/sfr3.html) |
| term.html | [term.html](https://github.com/dk14/warriors/blob/main/term.html) |
| uni.js | [uni.js](https://github.com/dk14/warriors/blob/main/uni.js) |

*All files are located at the root of the repository and can be accessed directly via the links above.*  

bird2.html - is a product-ready mobile game, not allowed for commercial use, author's property. Preparing to release on the AppStore/Android.
