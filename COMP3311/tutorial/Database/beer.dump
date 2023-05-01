--
-- PostgreSQL database dump
--

-- Dumped from database version 12.3
-- Dumped by pg_dump version 12.3

SET statement_timeout = 0;
SET lock_timeout = 0;
SET idle_in_transaction_session_timeout = 0;
SET client_encoding = 'UTF8';
SET standard_conforming_strings = on;
SELECT pg_catalog.set_config('search_path', '', false);
SET check_function_bodies = false;
SET xmloption = content;
SET client_min_messages = warning;
SET row_security = off;

--
-- Name: barname; Type: DOMAIN; Schema: public; Owner: -
--

CREATE DOMAIN public.barname AS character varying(30);


--
-- Name: beername; Type: DOMAIN; Schema: public; Owner: -
--

CREATE DOMAIN public.beername AS character varying(50);


--
-- Name: drinkername; Type: DOMAIN; Schema: public; Owner: -
--

CREATE DOMAIN public.drinkername AS character varying(20);


SET default_tablespace = '';

SET default_table_access_method = heap;

--
-- Name: bars; Type: TABLE; Schema: public; Owner: -
--

CREATE TABLE public.bars (
    name public.barname NOT NULL,
    addr character varying(20),
    license integer NOT NULL
);


--
-- Name: beers; Type: TABLE; Schema: public; Owner: -
--

CREATE TABLE public.beers (
    name public.beername NOT NULL,
    brewer character varying(40) NOT NULL,
    style character varying(40)
);


--
-- Name: drinkers; Type: TABLE; Schema: public; Owner: -
--

CREATE TABLE public.drinkers (
    name public.drinkername NOT NULL,
    addr character varying(30) NOT NULL,
    phone character(10) NOT NULL
);


--
-- Name: frequents; Type: TABLE; Schema: public; Owner: -
--

CREATE TABLE public.frequents (
    drinker public.drinkername NOT NULL,
    bar public.barname NOT NULL
);


--
-- Name: likes; Type: TABLE; Schema: public; Owner: -
--

CREATE TABLE public.likes (
    drinker public.drinkername NOT NULL,
    beer public.beername NOT NULL
);


--
-- Name: sells; Type: TABLE; Schema: public; Owner: -
--

CREATE TABLE public.sells (
    bar public.barname NOT NULL,
    beer public.beername NOT NULL,
    price double precision
);


--
-- Data for Name: bars; Type: TABLE DATA; Schema: public; Owner: -
--

COPY public.bars (name, addr, license) FROM stdin;
Australia Hotel	The Rocks	123456
Coogee Bay Hotel	Coogee	966500
Lord Nelson	The Rocks	123888
Marble Bar	Sydney	122123
Regent Hotel	Kingsford	987654
Royal Hotel	Randwick	938500
Local Taphouse	Darlinghurst	884488
\.


--
-- Data for Name: beers; Type: TABLE DATA; Schema: public; Owner: -
--

COPY public.beers (name, brewer, style) FROM stdin;
80/-	Caledonian	Scotch Ale
Amber Ale	James Squire	Amber Ale
Bigfoot Barley Wine	Sierra Nevada	Barley Wine
Burragorang Bock	George IV Inn	Bock
Chestnut Lager	Bridge Road Brewers	Lager
Crown Lager	Carlton	Lager
Fosters Lager	Carlton	Lager
India Pale Ale	James Squire	IPA
Invalid Stout	Carlton	Stout
Melbourne Bitter	Carlton	Lager
New	Toohey's	Lager
Nirvana Pale Ale	Murray's	Pale Ale
Old	Toohey's	Dark Lager
Old Admiral	Lord Nelson	Strong Ale
Pale Ale	Sierra Nevada	Pale Ale
Four Wives	James Squire	Pilsener
Jack of Spades	James Squire	Porter
Nine Tales	James Squire	Amber Ale
Premium Lager	Cascade	Lager
Red	Toohey's	Lager
Sink the Bismarck	Brew Dog	Quintuple IPA
Sheaf Stout	Toohey's	Stout
Sparkling Ale	Cooper's	Golden Ale
Stout	Cooper's	Stout
Tactical Nuclear Penguin	Brew Dog	Quadruple Imperial Stout
Three Sheets	Lord Nelson	Pale Ale
Victoria Bitter	Carlton	Lager
name	brewer	style
1750 Export Porter	Kees	
4D	Dainton	Imperial Red Rye IPA
Age of Aquarius	Garage Project	NEIPA
Alexander	Rodenbach	Flanders Red Ale
Apollo After Dark	Hawkers	Imperial Stout
Astrolabe	Frenchies	Red Biere de Garde
Banana Pastry Stout	Hop Nation	Pastry Stout
Barley Griffin	Bentspoke	Pale Ale
BBARIS	Mismatch	Russian Imperial Stout
Berserker	Ekim	Amber IPA
Betelgeuse	Kaiju	Double Red Ale
Bigfoot	Sierra Nevada	Barleywine
Big Nut	Bentspoke	Dark IPA
Black Forest	Dainton	Russian Imperial Stout
Black Hawk	Black Hops	Imperial Stout
Black Supr Draught	Detour	Pale Ale
Bling Bling	Bridge Road	Imperial IPA
Blood Orange Kviek IPA	Urbanaut	IPA
Bloodshot Red IPA	Ekim	Red IPA
Blur Vines	Quiet Deeds	Hazy DIPA
Botany Bay Lager	One Drop	Lager
Bounty Hunter	Dainton	Stout
Cabin Fever	Hargreaves Hill	Double IPA
California IPA	Sierra Nevada	IPA
Caramel Fudge Stout	Kees	Imperial Stout
Cashmere	Pirate Life	IPA
Cashmere Cat	Wayward	Hazy IPA
Clockwork Tangerine	BrewDog	XPA
Chocolate Stout Nitro	Rogue	Stout
Combat Wombat	Rogue	Sour Hazy IPA
Common Ground	White Bay	Baltic Porter
Conductor's Special Reserve Porter	Quiet Deeds	Smoky Porter
Crankshaft	Bentspoke	IPA
Dark Rum Spiked Porter	Ekim	Porter
Day Trip	Hawkers	Double IPA
Daydreaming in Spring	Quiet Deeds	DDH Hazy Pale Ale
DDHImperial IPA	Frenchies	Imperial IPA
Demon Cleaner	Kaiju	West Coast IPA
Descent19	Bentspoke	Imperial Stout
Descent20	Bentspoke	Imperial Stout
Dolce Noir	White Bay	Imperial Stout
Double Vanilla Custard Pancake	One Drop	Imperial Nitro Thickshake IPA
Down The Hill	New England	IPA + Chai
Dramjet	Boatrocker	Imperial Stout
Dreaming of Oats	Hawkers	Hazy IPA
Dry Haze	Garage Project& Balter	Dry Hazy IPA
Ember's IPA	Moon Dog	Red IPA
Erebus	Big Shed	Imperial Stout
Everyone's	One Drop	Nitro Red Ale
F-11.1% Jet Black IImperial IPA	Hope	Black Imperial IPA
Fantastic Haze	Sierra Nevada	Imperial IPA
Flemm	Bentspoke	Flemish Red Ale
Flight Path	Stockade	Pale Ale
Freedom Unit	Hawkers	Triple NEIPA
Fresh Harvest IPA	Frenchies	IPA
Fudge Dredd	Daintaon	Porter
Fudge Stout	Beatnik	Stout
Galaxy Fart Blaster	West City	Kettle soured Double IPA
Hazelnut Brown Nectar	Rogue	Brown ale
Hazy Little Thing	Sierra Nevada	Hazy IPA
Hel & Verdoemenis	De Molen	Imperial Stout
Victory at Sea	Ballast Point	Imperial Porter
Holmes Brew	Tallboy and Moose	American Pale Ale
How's it Gosen?	Bentspoke	Gose
Huge Arker	Anderson Valley	Bourbon Barrel-aged
Hunt for Red Velvet	Prancing Pony	Imperial Red IPA
Hypehopopotamus	Mountain Culture	NEIPA
Imperial IPA	Hawkers	Imperial IPA
IPA	Detour	IPA
Imperial Mango Sour	Hope	Sour
Imperial Pink Grapefruit Sour	Hope	Sour
India Red Ale	Prancing Pony	****\n
Intergalatic Lovechild	Quiet  Deeds	Sour + Hazy
Juice Stand	Alesmith	Hazy IPA
Jumping the Shark 2015	Moon Dog	Imperial Rye Stout
Jumping the Shark 2019	Moon Dog	Imperial Stout
Kamchatka	Frenchies	Biere de Garde Noir
Lager	Balter	Lager
Lark Barrel-aged Imperial JSP III	Wolf in the Willows	Imperial Porter
Lizard's Mouth	Figueroa	Imperial IPA
Major Mac	Yullis	Milk Stout
Matcha IPA	Kizakura	IPA
Mega Hornet	Black Hops	Triple IPA
Melbourne Fog	Hop Nation	Hazy Pale Ale
Mind Haze	Firestone Walker	Hazy IPA
Moon Dancer	Black Hops	Hazy IPA
Mosaic Mango Sour	Urbanaut	Sour
New World IPA	One Drop	IPA
No Dreams Til Brooklyn	Garage Project- Other Half	NEIPA
Oakey Dokey Stout	Boatrocker	Stout
Oat Cream	Six String	Nazy IPA
Oatmeal Stout	Ocean Beach	Stout
Oceanna	Frenchies	Raspberry
Peak Conditions	Stone	Double IPA
Peanut Butter Pastry Stout	6.0	Peanut Butter
Quadzilla	One Drop	Pale Ale
Royal Fang	Tallboy and Moose	Red IPA
Red Right Hand	Grand Ridge	Imperial Red IPA
Red Nut	Bentspoke	Red IPA
Red Rye-ot	Willie	Red Rye IPA
Redliner IIRA	Otherside	Imperial Red Ale
Reeferendum	Chur	Hazy IPA
Refreshing Ale	Stockade	Pale Ale
Road Tripper	Little Bang	Double West Coast IPA
Sabro-only IPA	Akasha	IPA
Sabro IPA	Ballistic	IPA
Salted Caramel Brown Ale	3 Ravens	Brown Ale
Sculpin	Ballast Point	IPA
Shake and Shimmy	Gigantic	Hazy IPA
S.P.X	Kees	Wee Heavy
Snot Block	Tallboy and Moose	IPA
Splicer	Stockade	XPA
Sprocket	Bentspoke	IPA
Strange Brew	Six String	Oat Cream IPA
Sunrise Valley	Garage Project	Hazy IPA
Tequila Queen	Counter Culture	Margarita
The Big Bad Wolf	One Drop	Imperial Stout
The Dawn	Hop Nation	Double NEIPA
The Hop King	One Drop	IPA
The Pav is Ours	Moon Dog	Pale Ale
The Second Horseman	Quiet Deeds	Imperial Stout
Three Pholosophers	Ommegang	Quadrupel Ale
Thunder Hammer	Tallboy and Moose	Imperial IPA
Trail Ale	Detour	Pale Ale
Trinity Porter	Badlands	London Porter
Twisted Fate	One Drop	Imperial IPA
Ursa Major	Tallboy and Moose	American Brown Ale
Variations on a Theme IV	Boatrocker	Hazy Imperial IPA
Warning: May Contain Traces of Panther	Little Bang	Porter
Wattleseed Brown Ale	NOMAD	Brown Ale
Weaponized	Epic	West Coast IPA
West Coast IPA	Mr Banks	West Coast IPA
XPA	Detour	Pale Ale
Yakimanian	One Drop	IPA
Zen Garden	Clown Shoes	NEIPA
\.


--
-- Data for Name: drinkers; Type: TABLE DATA; Schema: public; Owner: -
--

COPY public.drinkers (name, addr, phone) FROM stdin;
Adam	Randwick	9385-4444 
Gernot	Newtown	9415-3378 
John	Alexandria	9665-1234 
Andrew	Clovelly	9123-1234 
Justin	Mosman	9845-4321 
Helen	Coogee	9876-5432 
\.


--
-- Data for Name: frequents; Type: TABLE DATA; Schema: public; Owner: -
--

COPY public.frequents (drinker, bar) FROM stdin;
Andrew	Coogee Bay Hotel
Andrew	Local Taphouse
Andrew	Lord Nelson
Adam	Coogee Bay Hotel
Gernot	Lord Nelson
Gernot	Royal Hotel
Helen	Coogee Bay Hotel
Helen	Local Taphouse
John	Coogee Bay Hotel
John	Lord Nelson
John	Local Taphouse
John	Australia Hotel
Justin	Regent Hotel
Justin	Marble Bar
\.


--
-- Data for Name: likes; Type: TABLE DATA; Schema: public; Owner: -
--

COPY public.likes (drinker, beer) FROM stdin;
Adam	Crown Lager
Adam	Fosters Lager
Adam	New
Gernot	Premium Lager
Gernot	Sparkling Ale
John	80/-
John	Bigfoot Barley Wine
John	Pale Ale
John	Sink the Bismarck
John	Three Sheets
Justin	Sparkling Ale
Justin	Victoria Bitter
John	Jumping the Shark 2015
John	Jumping the Shark 2019
John	Lark Barrel-aged Imperial JSP III
John	Sculpin
John	Alexander
John	Sunrise Valley
John	India Red Ale
John	Victory at Sea
John	Red Nut
John	Huge Arker
Andrew	Victory at Sea
Andrew	Pale Ale
Andrew	Cashmere Cat
\.


--
-- Data for Name: sells; Type: TABLE DATA; Schema: public; Owner: -
--

COPY public.sells (bar, beer, price) FROM stdin;
Australia Hotel	Burragorang Bock	5.5
Australia Hotel	New	5
Coogee Bay Hotel	New	4.25
Coogee Bay Hotel	Old	4.5
Coogee Bay Hotel	Sparkling Ale	4.8
Coogee Bay Hotel	Victoria Bitter	4.3
Lord Nelson	Three Sheets	5.75
Lord Nelson	New	5
Lord Nelson	Old Admiral	5.75
Marble Bar	New	4.8
Marble Bar	Old	4.9
Marble Bar	Victoria Bitter	4.8
Regent Hotel	New	4.2
Regent Hotel	Victoria Bitter	4.2
Royal Hotel	New	4.3
Royal Hotel	Old	4.65
Royal Hotel	Victoria Bitter	4.3
Local Taphouse	Jumping the Shark 2019	10
Local Taphouse	Sculpin	7.5
Local Taphouse	Cashmere Cat	7
Local Taphouse	Big Nut	7.5
Local Taphouse	Red Nut	7
Local Taphouse	Pale Ale	7
Local Taphouse	Fantastic Haze	7
Local Taphouse	Bling Bling	6
Local Taphouse	Dolce Noir	7
Local Taphouse	Dramjet	9
Local Taphouse	The Hop King	8
\.


--
-- Name: bars bars_pkey; Type: CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.bars
    ADD CONSTRAINT bars_pkey PRIMARY KEY (name);


--
-- Name: beers beers_pkey; Type: CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.beers
    ADD CONSTRAINT beers_pkey PRIMARY KEY (name);


--
-- Name: drinkers drinkers_pkey; Type: CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.drinkers
    ADD CONSTRAINT drinkers_pkey PRIMARY KEY (name);


--
-- Name: frequents frequents_pkey; Type: CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.frequents
    ADD CONSTRAINT frequents_pkey PRIMARY KEY (drinker, bar);


--
-- Name: likes likes_pkey; Type: CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.likes
    ADD CONSTRAINT likes_pkey PRIMARY KEY (drinker, beer);


--
-- Name: sells sells_pkey; Type: CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.sells
    ADD CONSTRAINT sells_pkey PRIMARY KEY (bar, beer);


--
-- Name: frequents frequents_bar_fkey; Type: FK CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.frequents
    ADD CONSTRAINT frequents_bar_fkey FOREIGN KEY (bar) REFERENCES public.bars(name);


--
-- Name: frequents frequents_drinker_fkey; Type: FK CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.frequents
    ADD CONSTRAINT frequents_drinker_fkey FOREIGN KEY (drinker) REFERENCES public.drinkers(name);


--
-- Name: likes likes_beer_fkey; Type: FK CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.likes
    ADD CONSTRAINT likes_beer_fkey FOREIGN KEY (beer) REFERENCES public.beers(name);


--
-- Name: likes likes_drinker_fkey; Type: FK CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.likes
    ADD CONSTRAINT likes_drinker_fkey FOREIGN KEY (drinker) REFERENCES public.drinkers(name);


--
-- Name: sells sells_bar_fkey; Type: FK CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.sells
    ADD CONSTRAINT sells_bar_fkey FOREIGN KEY (bar) REFERENCES public.bars(name);


--
-- Name: sells sells_beer_fkey; Type: FK CONSTRAINT; Schema: public; Owner: -
--

ALTER TABLE ONLY public.sells
    ADD CONSTRAINT sells_beer_fkey FOREIGN KEY (beer) REFERENCES public.beers(name);


--
-- PostgreSQL database dump complete
--
