% This class file is provided for authors submitting to the
% Genetics Society of America's GENETICS Journal
%
% Version: 1.11, 2022/04/01
%
% Produced by GSA and Overleaf (www.overleaf.com)
%
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{gsajnl}[2022/04/01, v1.11]
\AtEndOfClass{\RequirePackage{microtype}}

% Options for element switching
\RequirePackage{xifthen}
\newboolean{displaycopyright}
\newboolean{displaylineno}
\setboolean{displaylineno}{false}

\DeclareOption{lineno}{\setboolean{displaylineno}{true}}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{extarticle}}
\ProcessOptions*
\LoadClass{extarticle}

% April 16, 2016:
% Line numbers
% v1.8 April 12, 2018: make sure line numbers are
% displayed in outer margins of columns; so
% remove "running" option somehow gets it right
\RequirePackage[switch,pagewise]{lineno}
%v1.11 April 1, 2022: re-add line numbers that were accidentally removed in 1.10


% Fonts and language
\RequirePackage[utf8]{inputenc}
\RequirePackage[english]{babel}
\RequirePackage{amsmath,amsfonts,amssymb}
\RequirePackage{mathpazo}
\RequirePackage[scaled]{helvet}
\RequirePackage[T1]{fontenc}
\RequirePackage{url}
\RequirePackage[colorlinks=true, allcolors=blue]{hyperref}
\RequirePackage{lettrine}

\newcommand{\watermarkfont}{\color{black50}\normalfont\fontsize{10}{12}\selectfont}
\newcommand{\headerfont}{\normalfont\fontsize{8}{10}\selectfont}
\newcommand{\headerifont}{\normalfont\fontsize{7}{9}\selectfont}
\newcommand{\titlefont}{\color{color3}\normalfont\sffamily\bfseries\fontsize{18}{22}\selectfont}
\newcommand\corresfont{\fontsize{9}{11}\selectfont}
\newcommand{\datesfont}{\normalfont\sffamily\itshape\fontsize{8}{10}\selectfont}
\renewcommand\UrlFont{\color{color1}\sffamily}
\newcommand{\absfont}{\normalfont\sffamily\linespread{1}\fontsize{8.9}{11}\selectfont}
\newcommand{\absheadfont}{\color{color3}\normalfont\sffamily\fontsize{9.4}{11}\selectfont}
\newcommand{\keywordsfont}{\normalfont\sffamily\linespread{1}\fontsize{8.9}{11}\selectfont}
\newcommand{\keywordheadfont}{\normalfont\sffamily\fontsize{7.8}{9}\selectfont\bfseries}
\newcommand{\copyrightfont}{\normalfont\sffamily\fontsize{7}{9}\selectfont}


\RequirePackage{datetime}

\newdateformat{monthyeardate}{%
  \monthname[\THEMONTH] \THEYEAR}

\RequirePackage{enumitem}
\setlist[itemize]{noitemsep}


% Author and affiliation
\RequirePackage{authblk}
\setlength{\affilsep}{9pt}
\renewcommand\Authfont{\color{color0}\fontsize{9.5}{11}\sffamily\selectfont}
\renewcommand\Affilfont{\color{color0}\fontsize{6.5}{9}\selectfont}
% \makeatletter
\renewcommand\AB@affilsep{\reset@font\protect\Affilfont}
\renewcommand\AB@affilsepx{\reset@font\protect\\\protect\Affilfont}
%\renewcommand\AB@affilsepx{, \protect\Affilfont}
% \makeatother
\renewcommand\Authands{ and }

% Choose article type
\newcommand*{\articletype}[1]{%
  \RequirePackage{styles/#1}}

% Copyright statement
\RequirePackage{textcomp} % For copyright symbol styling
\newcommand{\copyrightstatement}{Copyright \, \textcopyright\, \the\year{} by the Genetics Society of America}

% v1.6: Remove copyright statement from PDF
\AtBeginDocument{\setboolean{displaycopyright}{false}}

% Graphics, tables and other formatting
\RequirePackage{graphicx,xcolor}
\RequirePackage{colortbl}
\RequirePackage{booktabs}
\RequirePackage{tikz}
\RequirePackage{algorithm}
\RequirePackage[noend]{algpseudocode}
\RequirePackage{changepage}
\RequirePackage[left=48pt,%
                right=42pt,%
                top=48pt,%
                bottom=60pt,%
                headheight=15pt,%
                headsep=10pt,%
                letterpaper,twoside]{geometry}%
\RequirePackage[labelfont={bf,sf},%
                list=no,%
                labelsep=space,%
                figurename=Figure,%
                singlelinecheck=off,%
                justification=RaggedRight]{caption}
\setlength{\columnsep}{24pt} % Distance between the two columns of text
\setlength{\parindent}{12pt} % Paragraph indent

% Set document color scheme
\definecolor{black50}{gray}{0.5} % 50% black for hrules
\definecolor{color0}{RGB}{0,0,0} % Base color
\definecolor{color1}{RGB}{59,90,198} % unused
\definecolor{color3}{RGB}{0,76,113} %
% color2 defined by the specific article type style file

% Bibliography
\usepackage{natbib} \bibpunct{(}{)}{;}{author-year}{}{,}
\bibliographystyle{genetics}
\addto{\captionsenglish}{\renewcommand{\refname}{Reference List}}
\setlength{\bibsep}{0.0pt}

% Table style
\arrayrulecolor{color0} % Set the color of the horizontal rules
\renewcommand{\arraystretch}{1.5} % Increased line spacing
\captionsetup[table]{position=below} % Reduce spacing below caption

% Algorithm style
% \makeatletter
\newcommand\fs@coloruled{\def\@fs@cfont{\bfseries}\let\@fs@capt\floatc@coloruled
  \def\@fs@pre{\kern2pt}%
  \def\@fs@post{\kern2pt{\color{color2}\hrule}\relax}%
  \def\@fs@mid{\kern2pt{\color{color2}\hrule}\kern2pt}%
  \let\@fs@iftopcapt\iftrue}
% \makeatother

\floatstyle{coloruled}
\restylefloat{algorithm}

% Headers and footers
\RequirePackage{fancyhdr}  % custom headers/footers
\RequirePackage{lastpage}  % Number of pages in the document
        % Enables the custom headers/footers

\newif\ifslugprint\global\slugprintfalse

\fancypagestyle{firststyle}{
   \fancyhead[LO,RE,LE,RO]{}
   \ifslugprint\fancyhead[R]{\slugline}\else\fi%
   \fancyhead[L]{\firstpageimage}
   % v1.6: Remove volume and month information
%    \fancyfoot[R]{\footnotesize Genetics, Vol. XXX, XXXX–XXXX \hspace{1em} \monthyeardate\today \hspace{2em} \thepage\ }
}

\renewcommand{\headrulewidth}{0pt}% % No header rule
\renewcommand{\footrulewidth}{0pt}% % No footer rule

%% 13 July 2016: make sure sections are unnumbered
\setcounter{secnumdepth}{0}
\setcounter{tocdepth}{0}

% Section/subsection/paragraph set-up
\RequirePackage[explicit]{titlesec}
\renewcommand{\thesubsection}{\Alph{subsection}}

\titleformat{\section}
  {\large\sffamily\bfseries\color{color3}}
  {\thesection.}
  {0.5em}
  {#1}
  []
\titleformat{name=\section,numberless}
  {\large\sffamily\bfseries\color{color3}}
  {}
  {0em}
  {#1}
  []
\titleformat{\subsection}
  {\bfseries\fontsize{10}{12}\selectfont}
  {\thesubsection.}
  {0.5em}
  {#1}
  []
\titleformat{\subsubsection}[runin]
  {\sffamily\bfseries\itshape}
  {\thesubsubsection.}
  {0.5em}
  {#1}
  []
\titleformat{\paragraph}[runin]
  {\sffamily\small\bfseries}
  {}
  {0em}
  {#1}
\titlespacing*{\section}{0pc}{3ex \@plus4pt \@minus3pt}{5pt}
\titlespacing*{\subsection}{0pc}{2.5ex \@plus3pt \@minus2pt}{2pt}
\titlespacing*{\subsubsection}{0pc}{2ex \@plus2.5pt \@minus1.5pt}{2pt}
\titlespacing*{\paragraph}{0pc}{1.5ex \@plus2pt \@minus1pt}{12pt}

% Article meta data additional fields
\newcommand{\runningauthor}[1]{\def\@runningauthor{#1}}
%% Backward compatibility
\newcommand{\correspondingauthor}[1]{\runningauthor{#1}}
\newcommand{\keywords}[1]{\def\@keywords{#1}}
\newcommand{\runningtitle}[1]{\def\@runningtitle{#1}}

\newcommand{\keywordname}{{\keywordheadfont Number of Words:}} % Defines the keywords heading name

% Colored margin box
%\newcommand{\marginmark}{
%\begin{textblock}{2}(200,9.5)
%\begin{tikzpicture}
%\fill[color=color2] (0,0) rectangle (1.2,0.25);
%\end{tikzpicture}
%\end{textblock}
%}

\newcommand{\marginmark}{
\begin{textblock}{2}(200,9.5)
\begin{tikzpicture}
\fill[color=color2] (0,0) rectangle (1.2,0.25);
\end{tikzpicture}
\end{textblock}
}


\def\xabstract{abstract}
\long\def\abstract#1\end#2{\def\two{#2}\ifx\two\xabstract
\long\gdef\theabstract{\ignorespaces#1}
\def\go{\end{abstract}}\else
\typeout{^^J^^J PLEASE DO NOT USE ANY \string\begin\space \string\end^^J
COMMANDS WITHIN ABSTRACT^^J^^J}#1\end{#2}
\gdef\theabstract{\vskip12pt BADLY FORMED ABSTRACT: PLEASE DO
NOT USE {\tt\string\begin...\string\end} COMMANDS WITHIN
THE ABSTRACT\vskip12pt}\let\go\relax\fi
\go}

% Set environment for abstract content and styling
\newcommand{\abscontent}{
\noindent
{%
\parbox{\dimexpr\linewidth}{%
    {\absheadfont\bfseries Abstract}\vskip3.5pt \absfont \theabstract
}%
\vskip15.5pt%
\noindent
\parbox{\dimexpr\linewidth-2\fboxsep\relax}{%
 %% v1.8: turn on line numbers

{\keywordsfont\keywordname}\hspace*{0.1em} \keywordsfont \@keywords%
}%
}%
}%

% Custom title page
\renewcommand{\@maketitle}{\bgroup\setlength{\parindent}{0pt}
{%
\vskip10pt%
{\raggedright \titlefont \@title\vskip13pt}%
{\raggedright \@author\vskip9.5pt}
\ifx\@corres\undefined\vskip6.5pt\else\@corres\vskip11.5pt\fi%
}\egroup%
{%
\vskip12pt%
\abscontent
}%
\vskip25pt%
}%

% Other packages
\RequirePackage{enumitem} % For reducing bullet list item separation

\RequirePackage{tabularx}

\RequirePackage[flushmargin,ragged]{footmisc}

\newlength{\myFootnoteWidth}%
\newlength{\myFootnoteLabel}%
\setlength{\myFootnoteLabel}{0.5em}
\renewcommand{\@makefntext}[1]{%
  \setlength{\myFootnoteWidth}{\columnwidth}%
  \addtolength{\myFootnoteWidth}{-\myFootnoteLabel}%
  \noindent\makebox[\myFootnoteLabel][r]{\@makefnmark\ }%
  \parbox[t]{\myFootnoteWidth}{#1}
  }

\newdimen\footrulechange
\footrulechange\columnwidth
% Commands to set the footnote for the front page.
\renewcommand{\footnoterule}{%
  \kern -3pt
  {\color{black50} \hrule width \footrulechange height 0.5pt}
  \kern 2.5pt
}

\newcommand{\@authfootnote}[2]{%
  \begingroup
  \setlength{\myFootnoteLabel}{0em}
  \renewcommand\thefootnote{}\footnote{\footnotelayout\copyrightfont\textsuperscript{#1}#2}%
   \endgroup%
}

\newcommand\blfootnote[1]{%
  \@authfootnote{}{#1}%
%   \begingroup
%   \setlength{\myFootnoteLabel}{0em}
%   \renewcommand\thefootnote{}\footnote{#1}%
%   \addtocounter{footnote}{-1}%
%   \addtocounter{Hfootnote}{-1}%
%   \endgroup%
}
\newcommand\correspondingauthoraffiliation[2][]{%
  \gdef\@corres{\corresfont\textsuperscript{#1}#2}%
}

\def\dates#1{\gdef\@dates{#1}}

\def\rec#1{\textbf{Recevied:} #1.}
\def\rev#1{\textbf{Revised:} #1}
\def\acc#1{\textbf{Accepted:} #1}

\newcommand{\equalcontrib}[1]{\@authfootnote{#1}{These authors contributed equally to this work.}}

\newcommand{\firstpagefootnote}{\footrulechange\textwidth%
\blfootnote{\hsize\textwidth%doi: 10.1534/genetics.XXX.XXXXXX \\%
\ifx\@dates\undefined\vskip0pt\else\@dates\vskip0pt\fi%
Published by Oxford University Press on behalf of Genetics Society of America \the\year. This work is written by US Government employees and is in the public
domain in the US.
}}

\newenvironment{tableminipage}[1]{\begin{minipage}{#1}\renewcommand\footnoterule{ \kern -1ex}%
\setlength{\myFootnoteLabel}{0.5em}%
}{\end{minipage}}

\def\firstpagebreak{\break\newpage\noindent}

% Package to enable absolute positioning of figures
\RequirePackage[absolute,overlay]{textpos}
\setlength{\TPHorizModule}{1mm}
\setlength{\TPVertModule}{1mm}
\textblockorigin{0mm}{0mm} % start everything near the top-left corner
