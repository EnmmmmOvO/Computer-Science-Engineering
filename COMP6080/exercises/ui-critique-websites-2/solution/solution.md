## Go through and rip apart websites from UI perspective (2)

Navigate to [https://linktr.ee/s/pricing/](https://linktr.ee/s/pricing/) and analyse the page from a UI perspective.

Assume the role of a user who wants to use Linktree and wants to find the best plan to subscribe to.

Take note of:
- Basic Visual Design Principles
- Visual Hierarchy
- Affordances

> Disable AdBlock for this. This analysis was done on 28/01/2021. The page may change from then til now.
> 
> Scroll down past this analysis for notes on what the three sections entail.
>
> ### **Basic Visual Design Principles**
> - The comparison tables and the summary at the top of the page follows a pattern similar to the 12-grid, which allows for nice responsive design. The summaries at the top of the page decreases from 4 to 1 per row, depending on the width of the screen.
> - Only one font family is used - ensuring visual consistency
> - Colour palette is cyan, purple, aqua, which are not harmonious, but effective in accentuating different elements of the page
> - Header bar is clean, elements are separated clearly horizontally, with each element having enough horizontal margins
> - Each section of comparison tables is separated clearly with vertical margins, and colour choice
>
> ### **Visual Hierarchy**
> - There is a clear heirarchy of typography - larger and bolded text indicates important information or titles
> - Text that indicates the purpose of each comparison table is significantly larger than the text in the table, and draws attention to the table's purpose
> - Text that indicates an active state (Monthly or Annual at the top of the page) is either black or light grey - the more pronounced text indicates which toggle state is currently active
> - There is good use of colour to draw attention to certain plans or important elements, such as the PRO plan, or the "Save with annual plans" tag next to the "Annual" toggle
> - In each comparison table, elements that are included in the plan are marked as a purple tag, and those that are not are marked as a light grey cross - making it very easy to differentiate between the plans
> - Colour use is slightly inconsistent - the PRO plan is highlighted in purple at the top of the page, but the fixed header as the user scrolls down highlights the "Join for Free" button rather than the "Get Pro" button.
> - Main attention drawing colour (Purple) is a good contrast with the white background, drawing attention to the highlighted element
> - Comparison tables, the cells, and the plan summaries are repeated to ensure visual consistency
> 
> ### **Affordances**
> - The buttons in the header are explicit affordances, as are buttons that move the user further along the subscription flow
> - Pattern affordances include the drop down buttons in the left most cells of the comparison tables - allowing the user to get more information about a particular feature while ensuring height consistency between cells
> - The link directory, as well as the social media links at the bottom of the page are also pattern affordances.
> - The Monthly / Annual toggle state is also a pattern affordance


> ## Things to look for from a UI perspective
> - ### Ensuring users aren't scared (**Basic Visual Design Principles**)
>   - Do that using alignment, such as with Bootstrap 12-grids
>     - 12-grid because 12 can be divided evenly by 1, 2, 3, 4, 6.
>   - Consistent fonts
>     - Use at most 2 different font families either a nice font or a font pairing
>   - Harmonious set of colours
>     - Commonly includes a primary hue with variants, a secondary hue and greyscale
>     - Harmonious colours have the same hue values (H value in a HSL representation)
> 
> - ### Make it easier to find things (**Visual Hierarchy**)
>   - Size - bigger means important
>   - Colour - brighter means important
>   - Contrast - contrasting things draw attention
>   - Spacing - big margins create importance
>   - Alignment - misaligned things draw attention
>   - Repetition - puts things on the same level
> 
> - ### Make it easier to do something (**Affordances**)
>   - An afforance is the visual properties of an element that lets the user know they can do something with it (e.g. a button on a web page)
>     - Explicit affordances (Tells people how to interact) - "Click here" to do something
>     - Pattern affordances uses a common pattern to imply an interaction is possible - e.g. underlined blue text implies a link
>     - False affordances looks like an element would do something it can't do - avoid doing these