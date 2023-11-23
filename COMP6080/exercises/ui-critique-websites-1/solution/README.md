## Go through and rip apart websites from UI perspective (1)

Navigate to [https://www.youtube.com](https://www.youtube.com) and analyse the page from a UI perspective.

Assume the role of a user who is scrolling through the homepage, looking for a video to watch.

Take note of:
- Basic Visual Design Principles
- Visual Hierarchy
- Affordances

> You might want to do this in a private browser session to stop students from snooping in on your recommendations.
>
> Disable AdBlock for this. This analysis was done on 28/01/2021. The page may change from then til now.
> 
> Scroll down past this analysis for notes on what the three sections entail.
>
> ### **Basic Visual Design Principles**
> - The main scrolling component of the homepage utilises a 12-grid which allows for nice responsive design - the number of thumbnails in a row decreases from 6 to 1 depending on the width of the screen. The size of these thumbnails are such that the image, and all text details are clearly legible
> - Only one font family is used - ensuring visual consistency
> - Colour palette being used is red and then greyscale. Blue is used for the sign in prompt. Not the most harmonious use of colours, but it helps make certain elements (Like the sign in button and the logo) distinct
> - Side bar is not scrolled when a user scrolls the Videos section of the homepage
> - Header bar is clean, minimal use of text to indicate meaning (Pattern Affordances)
> - There is the use of horizontal bars to indicate a break between sections
> - You can comment on banner ads that pop up on the homepage when you're scrolling if you see them.
> - As the main videos part of the page is infinitely scrolling, a user will have to use the sidebar to access settings or the YouTube directory. If a user mouses over the side bar, they will see the scrollbar (Pattern Affordance)
>
> ### **Visual Hierarchy**
> - All the thumbnails and titles are the same size, in terms of image size, and font size
> - When scrolling through, a user will encounter different sections for different categories, e.g. "Trending" or "COVID-19" - the font size is larger than the other parts of the homepage to draw attention to it
> - Due to the limited colour palette, they use boldface, and greyscale to convey importance. The title of each video is bolded and black, but the video creator's name, the viewcount and the timestamp is grey
> - The choice of text colour (No matter if it is light theme or dark theme) is always well contrasted with the background, does the same thing as the point above
> - Large vertical margins (combined with the horizontal bar) when a user encounters a category in the home page indicates importance
> - The videos are uniform and repetitive, putting things on the same level of importance
> 
> ### **Affordances**
> - Hamburger menu button is a pattern affordance, so is the triple vertical dot on the top right for a settings drop down
> - The buttons on the side bar are also pattern affordances (For "Home", "Explore", "Subscriptions"), as the "Home" button is defaulted to being a different colour than the others, implying that the other buttons can be used to mutate the homepage display. This is also helped by the icon and text in these buttons being aligned
> - The logo is also a pattern affordance - users expect that clicking on the logo will navigate to the homepage again
> - The videos themselves are kind of a pattern affordance - not a very good one. They are links, but do not indicate that they are links unless a user hovers over it. The fact that they are links is not immediately obvious to a first time user.
> - Explicit affordances include the "Sign In" button, and the searchbar.


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